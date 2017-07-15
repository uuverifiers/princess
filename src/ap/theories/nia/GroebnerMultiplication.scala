/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2017 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.theories.nia

import ap._
import ap.parser._
import ap.theories._
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.terfor.{TermOrder, ConstantTerm, OneTerm, Formula}
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.basetypes.IdealInt
import ap.util.{Timeout, Seqs}

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer}


/**
 * Implementation of a theory of non-linear integer arithmetic.
 * Currently the theory does Groebner basis calculation followed
 * by interval propagation.
 */
object GroebnerMultiplication extends MulTheory {

  val mul = new IFunction("mul", 2, true, false)
  val _mul = new Predicate("mul", 3)
  val functions = List(mul)
  val predicates = List(_mul)

  val axioms = Conjunction.TRUE
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig : Signature.PredicateMatchConfig =
    Map(_mul -> Signature.PredicateMatchStatus.None)
  val functionalPredicates = predicates.toSet
  override val singleInstantiationPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)
  val triggerRelevantFunctions : Set[IFunction] = Set()

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    theories match {
      case Seq(GroebnerMultiplication) => true
      case _ => false
    }

  /**
   * Conversion functions
   */

  /**
   * Converts an LinearCombination (Princess) to a Polynomial (Groebner)
   */
  def lcToPolynomial(lc : LinearCombination)
                    (implicit ordering : MonomialOrdering) : Polynomial = {
    var retPoly = Polynomial(List())

    for ((coeff, term) <- lc) {
      retPoly +=
        (term match {
          case (OneTerm) =>
            new Term(coeff, Monomial(List()))
          case (x : ConstantTerm) =>
            new Term(coeff, Monomial(List((x, 1))))
        })
    }
    retPoly
  }

  // Converts an atom (Princess) to a Polynomial (Groebner)
  def atomToPolynomial(a : Atom)
                      (implicit ordering : MonomialOrdering) : Polynomial =
    lcToPolynomial(a(0))*lcToPolynomial(a(1)) - lcToPolynomial(a(2))


  //////////////////////////////////////////////////////////////////////////////

  def plugin = Some(new Plugin {

    private var oldGBSrc : Seq[Atom] = List()
    private var oldGBRes : Option[(Basis, Seq[Atom], MonomialOrdering)] = None

    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      handleGoalAux(goal, false)

    /**
     * Buchberger algorithm
     * This function will modify the contents of the argument
     * <code>unprocessed</code>
     */
    private def buchberger(unprocessed : Basis) : Basis = {
      implicit val _ = unprocessed.ordering

      // First move from unprocessed =>
      //   passive - reducing all polynomials in active
      // Then move from passive to active =>
      //   adding all s-polynomials to unprocessed

      val active, passive = new Basis

      while (!unprocessed.isEmpty || !passive.isEmpty) {
        Timeout.check

/*
println("======================")

println
println("Active:")
println(active)

println
println("Passive:")
println(passive)

println
println("Unproc:")
println(unprocessed)
*/

        if (!unprocessed.isEmpty) {

          // Move one polynomial from unprocessed to passive
          val (chosen, chosenLabel) = unprocessed.get
//println("next: " + chosen)
          val (newPoly, newLabel) =
            active.reducePolynomial(passive, chosen, chosenLabel)

          // If the new polynomial is reduced to zero, reiterate
          if (!newPoly.isZero) {
            val reducedActive  = active.reduceBy(newPoly, newLabel)
            val reducedPassive = passive.reduceBy(newPoly, newLabel)

            unprocessed add reducedActive
            unprocessed add reducedPassive

            passive.add(newPoly, newLabel)
          }

        } else if (!passive.isEmpty) {

          val (newPoly, newLabel) = passive.get

          for (p <- active.polyIterator)
            if (newPoly.lt hasCommonVariables p.lt) {
              val spol = newPoly spol p
              if (!spol.isZero)
                unprocessed.add(spol, newLabel | (active labelFor p))
            }

          active.add(newPoly, newLabel)

        }
      }

      active
    }


    /**
     * Converts Polynomial (Groebner) to an Atom (Princess)
     * PRE: p is linear
     */
    private def polynomialToAtom(p : Polynomial)
                                (implicit order : TermOrder) : Conjunction = {
      def termToLc(t : Term) : LinearCombination = {
        if (t.m.pairs == Nil)
          t.c
        else
          l(t.c) * t.m.pairs.head._1
      }

      val terms =
        for (t <- p.terms; if (!t.isZero))
        yield termToLc(t)

      val LHS = (terms.tail).foldLeft(terms.head) ((t1,t2) => t1 + t2)
      conj(LHS === 0)
    }

    private def genMonomialOrder(predicates : Seq[Atom]) : MonomialOrdering = {
      var definedList = Set[ConstantTerm]()

      // Add all elements from LHS as defined
      for (a <- predicates)
        for (aa <- a(0).termIterator ++ a(1).termIterator) aa match {
          case OneTerm => ()
          case x : ConstantTerm => definedList += x
        }

      // Remove all elements that occurs on RHS from defined
      for (a <- predicates)
        for (aa <- a(2).termIterator) aa match {
          case OneTerm => ()
          case x : ConstantTerm =>
            if ((x.toString startsWith "all") ||
                (x.toString startsWith "ex") ||
                (x.toString startsWith "sc"))
              definedList -= x
        }

      // Fix-point computation to find the defined-set
      def genDefsymbols(predicates : Seq[Atom],
                        defined : Set[ConstantTerm],
                        undefined : List[ConstantTerm]) : List[ConstantTerm] =
        if (predicates.isEmpty) {
          undefined.reverse
        } else {
          val predIt = predicates.iterator
          while (predIt.hasNext) {
            val a = predIt.next

            var allDefined = true
            for (aa <- a(0).termIterator ++ a(1).termIterator) aa match {
              case OneTerm => ()
              case x : ConstantTerm =>
                if (!(defined contains x))
                  allDefined = false
            }

            if (allDefined)
              a(2)(0)._2 match {
                case OneTerm =>
                  return genDefsymbols(predicates diff List(a),
                                       defined, undefined)
                case (x : ConstantTerm) =>
                  return genDefsymbols(predicates diff List(a),
                                       defined + x, x :: undefined)
              }
          }
          undefined.reverse
        }

      val orderList = genDefsymbols(predicates, definedList, List())
      new PartitionOrdering(orderList,
                            new GrevlexOrdering(new ListOrdering(orderList)))
    }

    ////////////////////////////////////////////////////////////////////////////

    def handleGoalAux(goal : Goal,
                      calledFromSplitter : Boolean) : Seq[Plugin.Action] = {
      implicit val order = goal.order

// println("Groebner: " + goal.facts)

      // Fetch all predicates, if none nothing we can do
      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
      if (predicates.isEmpty)
        return List()

      val inequalities = goal.facts.arithConj.inEqs
      val disequalities = goal.facts.arithConj.negativeEqs

      val ineqOffset = predicates.size
      val negeqOffset = ineqOffset + inequalities.size

      def label2Assumptions(l : BitSet) : Seq[Formula] =
        for (ind <- l.toSeq) yield {
          if (ind < ineqOffset)
            predicates(ind)
          else if (ind < negeqOffset)
            InEqConj(inequalities(ind - ineqOffset), order)
          else
            NegEquationConj(disequalities(ind - negeqOffset), order)
        }

      val predicatesList = predicates.toList
      val (simplifiedGB, factsToRemove, monOrder) =
        if (oldGBSrc == predicatesList) {
//          println("Reusing ...")
          oldGBRes.get
        } else {
          // Create a monomial ordering
          implicit val monOrder = genMonomialOrder(predicates)
    
          val basis = new Basis
          var factsToRemove = List[ap.terfor.preds.Atom]()
    
          for ((a, index) <- predicates.iterator.zipWithIndex) {
            val p = atomToPolynomial(a)
    
            if (p.isZero)
              factsToRemove = a :: factsToRemove
            else
              basis.add(p, BitSet(index))
          }
 
          val gb = buchberger(basis)
          val simplified = gb.simplify

          oldGBSrc = predicatesList
          oldGBRes = Some((simplified, factsToRemove, monOrder))

          (simplified, factsToRemove, monOrder)
        }

      for (p <- simplifiedGB.containsUnit)
        // we have an inconsistency
        return List(Plugin.CloseByAxiom(
                             label2Assumptions(simplifiedGB labelFor p),
                             GroebnerMultiplication.this))

      implicit val xMonOrder = monOrder

      //////////////////////////////////////////////////////////////////////////

      val removeFactsActions =
        if (factsToRemove.isEmpty)
          List()
        else
          List(Plugin.RemoveFacts(conj(factsToRemove)))

      // Translate this to a linear system

      def makeMap(polylist : Seq[Polynomial]) : List[Monomial] = {
        var newmap = List[Monomial]()

        for (p <- polylist)
          for (t <- p.terms)
            if (!(newmap contains t.m)) {
              if (t.m.isLinear)
                newmap = t.m :: newmap
              else
                newmap = newmap ++ List(t.m)
            }
        newmap
      }

      def polyToRow(poly : Polynomial, map : List[Monomial]) : List[IdealInt] = {
        for (m <- map)
        yield {
          val termOpt = poly.terms find (_.m == m)
          termOpt match {
            case Some(term) => term.c
            case None => IdealInt.ZERO
          }
        }
      }

      def makeMatrix(polylist : Seq[Polynomial]) : Array[Array[IdealInt]] = {
        var monomialMap = makeMap(polylist)
        val list = for (p <- polylist) yield polyToRow(p, monomialMap)

        val array = Array.ofDim[IdealInt](list.length, monomialMap.length)

        for (i <- 0 until list.length)
          for (j <- 0 until list(i).length)
            array(i)(j) = list(i)(j)

        array
      }

      def rowToPolynomial(map : List[Monomial], row : Array[IdealInt]) = {
        var retPoly = Polynomial(List())
        for (i <- 0 until row.length;
          if (!row(i).isZero))
          retPoly += new Term(row(i), map(i))

        retPoly
      }

      // Did we find any linear formulas that can be propagated back?
      val linearEq = simplifiedGB.toArray
      if (!linearEq.isEmpty) {
        if (linearEq forall (_.isLinear)) {

          val actions =
            (for (p <- linearEq.iterator;
                  c = polynomialToAtom(p) /* ;
                  if !(goal reduceWithFacts !c).isFalse */)
             yield Plugin.AddAxiom(label2Assumptions(simplifiedGB labelFor p),
                                   c, GroebnerMultiplication.this)).toList
          
          if (!actions.isEmpty)
            return removeFactsActions ::: actions

        } else if (linearEq.size > 1) {

          val map = makeMap(linearEq)
          val m = makeMatrix(linearEq)
          val gaussian = new Gaussian(m)

          val implications =
            (for ((r, preLabel) <- gaussian.getRows.iterator;
                  poly = rowToPolynomial(map, r);
                  if (poly.isLinear))
             yield (polynomialToAtom(poly),
                    BitSet() ++
                      (for (ind <- preLabel.iterator;
                            ind2 <- simplifiedGB labelFor linearEq(ind))
                       yield ind2))).toList

          if (!implications.isEmpty)
            return removeFactsActions ::: (
                     for ((eq, label) <- implications)
                     yield Plugin.AddAxiom(label2Assumptions(label), eq,
                                           GroebnerMultiplication.this))
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // If Gröbner basis calculation does nothing
      // Lets try to do some interval propagation

      val preds =
        ((for ((a, n) <- predicates.iterator.zipWithIndex;
               poly = atomToPolynomial(a);
               if !poly.isZero)
          yield (poly, BitSet(n))) ++
         (for (p <- simplifiedGB.polyIterator)
          yield (p, simplifiedGB labelFor p))).toList

      val ineqs =
        (for ((lc, n) <- goal.facts.arithConj.inEqs.iterator.zipWithIndex)
         yield (lcToPolynomial(lc), BitSet(n + ineqOffset))).toList

      val negeqs =
        (for ((lc, n) <- goal.facts.arithConj.negativeEqs.iterator.zipWithIndex)
         yield (lcToPolynomial(lc), BitSet(n + negeqOffset))).toList

      val intervalSet = new IntervalSet(preds, ineqs, negeqs)

      intervalSet.propagate

      val intActions =
        filterActions(intervals2Actions(intervalSet, predicates,
                                        goal, label2Assumptions _), order)

      if (!intActions.isEmpty)
        return removeFactsActions ++ intActions

      // Do splitting
      if (calledFromSplitter)
        return List()

      goalState(goal) match {
        case Plugin.GoalState.Final =>
          // Split directly!
          removeFactsActions ::: (Splitter handleGoal goal).toList
        case _ =>
          val scheduleAction = Plugin.ScheduleTask(Splitter, 0)
          removeFactsActions ::: List(scheduleAction)
      }

    }

    ////////////////////////////////////////////////////////////////////////////

    private def filterActions(actions : Seq[Plugin.Action],
                              order : TermOrder)
                             : Seq[Plugin.Action] =
      actions filter (Plugin.isRelevantAxiomAction(_, order))

    private def intervals2Formula(intervalSet : IntervalSet,
                                  predicates : IndexedSeq[Atom],
                                  goal : Goal)
                                 : Conjunction = {
      implicit val _ = goal.order

      goal reduceWithFacts conj(
        for (Plugin.AddAxiom(_, f, _) <-
               intervals2Actions(intervalSet, predicates,
                                 goal, l => List()).iterator)
        yield f).negate
    }

    private def intervals2Actions(intervalSet : IntervalSet,
                                  predicates : IndexedSeq[Atom],
                                  goal : Goal,
                                  label2Assumptions : BitSet => Seq[Formula])
                                 : Seq[Plugin.Action] = {
      implicit val order = goal.order

      val intervalAtoms = new ArrayBuffer[(ArithConj, BitSet)]

      for ((ct, i, (ul, uu, gu), label) <- intervalSet.getIntervals) {

        if ((ul || uu) && i.lower == i.upper) {
          i.lower match {
            case IntervalVal(v) => intervalAtoms += ((ct === v, label))
            case _ => // nothing
          }
        } else {
          // Generate inequalities according to intervals
          if (ul) {
            i.lower match {
              case IntervalNegInf =>
              case IntervalPosInf => {
                intervalAtoms += ((ct > 0, label))
                intervalAtoms += ((ct < 0, label))
              }
              case IntervalVal(v) =>
                intervalAtoms += ((ct >= v, label))
            }
          }

          if (uu) {
            i.upper match {
              case IntervalNegInf => {
                intervalAtoms += ((ct > 0, label))
                intervalAtoms += ((ct < 0, label))
              }
              case IntervalVal(v) =>
                intervalAtoms += ((ct <= v, label))
              case IntervalPosInf =>
            }
          }
        }
      }

      //////////////////////////////////////////////////////////////////////////
      //
      // Generate linear approximations of quadratic terms using
      // cross-multiplication

      def enumBounds(i : Interval) : Iterator[(IdealInt, IdealInt)] =
        (i.lower match {
           case IntervalVal(v) => Iterator single ((IdealInt.ONE, v))
           case _ => Iterator.empty
         }) ++
        (i.upper match {
           case IntervalVal(v) => Iterator single ((IdealInt.MINUS_ONE, -v))
           case _ => Iterator.empty
         })

      val crossInEqs : Iterator[(ArithConj, BitSet)] =
        for ((a, predN) <- predicates.iterator.zipWithIndex;
             if (a(0).size == 1 && a(0).constants.size == 1 &&
                 a(1).size == 1 && a(1).constants.size == 1);
             ca0 = a(0).leadingTerm.asInstanceOf[ConstantTerm];
             ca1 = a(1).leadingTerm.asInstanceOf[ConstantTerm];
             (i0, l0) = intervalSet getLabelledTermInterval ca0;
             (i1, l1) = intervalSet getLabelledTermInterval ca1;
             (coeff0, bound0) <- enumBounds(i0 * a(0).leadingCoeff);
             (coeff1, bound1) <- enumBounds(i1 * a(1).leadingCoeff)) yield {
          ((a(2) * coeff0 * coeff1) -
             (a(0) * coeff0 * bound1) -
             (a(1) * coeff1 * bound0) +
             (bound0 * bound1) >= 0,
           (l0 | l1) + predN)
        }

      //////////////////////////////////////////////////////////////////////////

      (for ((f, label) <- intervalAtoms.iterator ++ crossInEqs;
            if !(goal reduceWithFacts !f).isFalse)
       yield (Plugin.AddAxiom(label2Assumptions(label), conj(f),
                              GroebnerMultiplication.this))).toList

    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Splitter handles the splitting when no new information can be deduced
     * 
     * Strategy:
     * 1) 
     */
    object Splitter extends TheoryProcedure 
    {
      def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
  
        // Extract all predicates
        val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
  
        if (predicates.isEmpty)
          return List()
  
        // An order is needed to construct polynomials, since Buchberger isn't used,
        // the order shouldn't matter.
        implicit val order = goal.order
        implicit val monOrder = new GrevlexOrdering(new StringOrdering)
        implicit val ctOrder = monOrder.termOrdering
  
//   println("Splitter: " + goal.facts)
  
        val preds =
          (for ((a, n) <- predicates.iterator.zipWithIndex;
                poly = atomToPolynomial(a);
                if !poly.isZero)
           yield (poly, BitSet(n))).toList

        val inequalities = goal.facts.arithConj.inEqs
        val disequalities = goal.facts.arithConj.negativeEqs
        val equalities = goal.facts.arithConj.positiveEqs

        val ineqOffset = predicates.size
        val negeqOffset = ineqOffset + inequalities.size
        val eqOffset = negeqOffset + disequalities.size

        def label2Assumptions(l : BitSet) : Seq[Formula] =
          for (ind <- l.toSeq) yield {
            if (ind < ineqOffset)
              predicates(ind)
            else if (ind < negeqOffset)
              InEqConj(inequalities(ind - ineqOffset), order)
            else if (ind < eqOffset)
              NegEquationConj(disequalities(ind - negeqOffset), order)
            else
              EquationConj(equalities(ind - eqOffset), order)
          }

        /**
         * Here follows the different splitting strategies
         * 
         */
  
        // General helper function, that find sets of ConstantTerms such that
        // all predicates are linearized
        // Since we have predicates of the form a(0)*a(1)=a(2), a simple (but incomplete?)
  
        def linearizers(predicates : List[ap.terfor.preds.Atom]) : Set[Set[ConstantTerm]] = {
  
          // Given the List [({x11, x12, ...}, {y11, y12, ...}), ({x21, ....]
          // returns {{x1*, x2*, x3* ...xn*}, {x1*, x2*, ... yn*}, ..., {y1*, y2*, ... yn*}}
  
          val predSet =
            for (p <- predicates)
            yield
              (p(0).constants, p(1).constants)
  
          val allConsts = order sort order.orderedConstants
          val allConstsSet = new MHashSet[ConstantTerm]
          allConstsSet ++= allConsts

          def isLinear : Boolean =
            predSet forall { case (s1, s2) => (s1 subsetOf allConstsSet) ||
                                              (s2 subsetOf allConstsSet) }

          if (isLinear)
            // minimise the set of chosen constants (greedily)
            for (c <- allConsts) {
              allConstsSet -= c
              if (!isLinear)
                allConstsSet += c
            }

          Set(allConstsSet.toSet)
        }
  
  
        def sphericalSplit(predicates : List[ap.terfor.preds.Atom],
                           intervalSet : IntervalSet)
                          : Iterator[(ArithConj, ArithConj, String, BitSet,
                                      Seq[Plugin.Action])] =  {
          throw new Exception("sphericalSplit not enabled!")
        }
  
  
        /**
          * Splits intervals that ranges from -Inf to +Inf on zero
          */
  
        def infinitySplit(intervalSet : IntervalSet,
                          targetSet : Set[ConstantTerm])
                         : Iterator[(ArithConj, ArithConj, String, BitSet,
                                     Seq[Plugin.Action])] = {
          (intervalSet.getAllIntervals.iterator.collect {
            case (c, i, label) if ((targetSet contains c) &&
                                   i.lower == IntervalNegInf &&
                                   i.upper == IntervalPosInf) => {
              val opt1 = (c >= 0)
              val opt2 = (c < 0)
              (opt1.negate, opt2.negate,
               "[-Inf, +Inf] split: " + opt1 + ", " + opt2,
               BitSet(),
               splitTermAt(c, IdealInt.ZERO))
            }
          })
        }
  
        def splitTermAt(x : ConstantTerm, mid : IdealInt) : Seq[Plugin.Action] =
          List(Plugin.AxiomSplit(
                List(),
                List((exists(_mul(List(l(x), l(1), l(v(0)))) & (v(0) <= mid)),
                      List()),
                     (exists(_mul(List(l(x), l(1), l(v(0)))) & (v(0) > mid)),
                      List())),
                GroebnerMultiplication.this))

        /**
         * Finds any possible split by finding a lower (upper) bound b on
         * any variable x and the form the split x = b V x > b (x = b V x < b)
         */ 
        def desperateSplit(intervalSet : IntervalSet,
                           targetSet : Set[ConstantTerm])
                          : Iterator[(ArithConj, ArithConj, String, BitSet,
                                      Seq[Plugin.Action])] = {
          val symbols = targetSet.toList.sortBy(_.name)
          val ac = goal.facts.arithConj

          for (x <- symbols.iterator;
               res <- (intervalSet getLabelledTermInterval x) match {
                 case (Interval(IntervalVal(ll),
                                IntervalVal(ul), _), _) if (ll < ul) => {
                   val mid = (ll + ul) / 2
                   val opt1 = ArithConj.conj(x <= mid, order)
                   val opt2 = ArithConj.conj(x > mid, order)
                   Iterator single ((opt1.negate, opt2.negate,
                                     "Interval split: " + opt1 + ", " + opt2,
                                     BitSet(), splitTermAt(x, mid)))
                 }
                 case (Interval(IntervalVal(ll), IntervalPosInf, _), label) => {
                   val opt1 = ArithConj.conj(x === ll, order)
                   val opt2 = ArithConj.conj(x > ll, order)
                   Iterator single ((opt1.negate, opt2.negate,
                                     "LowerBound split: " + opt1 + ", " + opt2,
                                     label, null))
                 }
                 case (Interval(IntervalNegInf, IntervalVal(ul), _), label) => {
                   val opt1 = ArithConj.conj(x === ul, order)
                   val opt2 = ArithConj.conj(x < ul, order)
                   Iterator single ((opt1.negate, opt2.negate,
                                     "UpperBound split: " + opt1 + ", " + opt2,
                                     label, null))
                 }
                 case _ =>
                   Iterator.empty
               })
          yield res
        }
  
        /**
         * Takes negative equations (i.e. x+y+... != 0) and splits them around
         * zero
         */
        def negeqSplit(intervalSet : IntervalSet,
                       negeqs : ap.terfor.equations.NegEquationConj,
                       targetSet : Set[ConstantTerm])
                      : Iterator[(ArithConj, ArithConj, String, BitSet,
                                 Seq[Plugin.Action])] =
          for (negeq <- negeqs.iterator;
               if (negeq.constants.size == 1);
               c = negeq.constants.iterator.next;
               if ((targetSet contains c) &&
                   (intervalSet getTermInterval c).containsInt(-negeq.constant));
               opt1 = (negeq > 0);
               opt2 = (negeq < 0))
          yield
            (opt1.negate, opt2.negate, "Negeq split on: " + negeq,
             null,
             List(Plugin.SplitDisequality(negeq, List(), List())))
  
        /**
         * Utilizes any gaps in an interval (i.e. x = [lb, -a] U [a, ub]) 
         *  and branches into two (i.e. x <= -a V x >= a)
         *
         */
        def gapSplit(intervalSet : IntervalSet,
                     targetSet : Set[ConstantTerm])
                    : Iterator[(ArithConj, ArithConj, String, BitSet,
                                Seq[Plugin.Action])] = {
          val gaps = intervalSet.getGaps
          (for ((term, interval, label) <- gaps.iterator;
                if (targetSet contains term))
          yield {
            val opt1 = (term < interval.gap.get._1)
            val opt2 = (term > interval.gap.get._2)
            (opt1.negate, opt2.negate,
             "Gap split on " + term + " using " + interval,
             label, null)
          })
        }

        ////////////////////////////////////////////////////////////////////////  
  
        val ineqPolys, negeqPolys = new ArrayBuffer[(Polynomial, BitSet)]

        def addFacts(conj : ArithConj) : Unit = {
          for ((lc, n) <- conj.inEqs.iterator.zipWithIndex)
            ineqPolys += ((lcToPolynomial(lc), BitSet(n + ineqOffset)))
          for ((lc, n) <- conj.positiveEqs.iterator.zipWithIndex) {
            ineqPolys += ((lcToPolynomial(lc), BitSet(n + eqOffset)))
            ineqPolys += ((lcToPolynomial(-lc), BitSet(n + eqOffset)))
          }
          for ((lc, n) <- conj.negativeEqs.iterator.zipWithIndex)
            negeqPolys += ((lcToPolynomial(lc), BitSet(n + negeqOffset)))
        }

        addFacts(goal.facts.arithConj)

        var contPropLoop = true
        var lastAlternative : Seq[Plugin.Action] = null
        while (contPropLoop) {
          contPropLoop = false

          val intervalSet =
            new IntervalSet(preds, ineqPolys.toList, negeqPolys.toList)
  
          intervalSet.propagate

          for ((_, _, l) <- intervalSet.getInconsistency)
            return List(Plugin.CloseByAxiom(label2Assumptions(l),
                                            GroebnerMultiplication.this))

          // Let the target set be the smallest set such that all
          // predicates are made linear
          val targetSet = linearizers(predicates.toList).toList
                             .sortWith((s1, s2) => s1.size > s2.size).head

          val alternatives =
            negeqSplit(intervalSet,
                       goal.facts.arithConj.negativeEqs, targetSet) ++
            gapSplit(intervalSet, targetSet) ++ 
            (Param.NONLINEAR_SPLITTING(goal.settings) match {
              case Param.NonLinearSplitting.Sign =>
                infinitySplit(intervalSet, targetSet) ++
                desperateSplit(intervalSet, targetSet)
              case Param.NonLinearSplitting.Spherical =>
                sphericalSplit(predicates.toList, intervalSet)
            })

          if (alternatives.hasNext) {
            val s@(opt1, opt2, _, label, actions) = alternatives.next

            if (Param.PROOF_CONSTRUCTION(goal.settings)) {
              // just apply the split that we found
//              println("Splitting: " + s)
              
              val splitActions =
                if (actions == null)
                  List(Plugin.AxiomSplit(label2Assumptions(label),
                                         List((conj(opt1), List()),
                                              (conj(opt2), List())),
                                         GroebnerMultiplication.this))
                else
                  actions

              val intActions =
                filterActions(intervals2Actions(intervalSet, predicates, goal,
                                                label2Assumptions _), order)
              val res = intActions ++ splitActions

//              println("res: " + res)
              return res

            } else {

              val opt1act = Conjunction.conj(opt1, order)
              val opt2act = Conjunction.conj(opt2, order)
              lastAlternative =
                List(Plugin.AddFormula(intervals2Formula(intervalSet,
                                                         predicates, goal)),
                     Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)),
                                           List(Plugin.AddFormula(opt2act)))))

              // check whether we might be able to close one of the branches
              // immediately, in which case we can focus on the other branch

              if ((goal reduceWithFacts opt1).isFalse) {
                addFacts(opt1.negate)
//                println("one further iteration, adding " + opt1.negate)
                contPropLoop = true
              } else if ((goal reduceWithFacts opt2).isFalse) {
                addFacts(opt2.negate)
//                println("one further iteration, adding " + opt2.negate)
                contPropLoop = true
              } else {
//                println("Splitting: " + s)

                return lastAlternative
              }
            }

          } else if (lastAlternative != null) {

            return lastAlternative

          } else {

            val intActions =
              filterActions(intervals2Actions(intervalSet, predicates,
                                              goal, label2Assumptions _), order)
            if (!intActions.isEmpty)
              return intActions

          }
        }

        val retList = handleGoalAux(goal, true)
        if (retList.isEmpty)
          throw new Exception("ERROR: No splitting alternatives found")
  
        retList
      }
    }
  })


  TheoryRegistry register this

  override def toString = "GroebnerMultiplication"
}
