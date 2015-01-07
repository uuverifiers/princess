/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2015 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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
import ap.terfor.{TermOrder, ConstantTerm, OneTerm}
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.basetypes.IdealInt
import ap.util.Timeout

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}


/**
 * Implementation of a theory of non-linear integer arithmetic.
 * Currently the theory does Groebner basis calculation followed
 * by interval propagation.
 */
object GroebnerMultiplication extends MulTheory {

  val mul = new IFunction("mul", 2, true, false)
  val functions = List(mul)

  val (predicates, axioms, totalityAxioms, _mul) = {
    val functionEnc = new FunctionEncoder (true, false)
    val predicates =
      for (f <- functions) yield (functionEnc addFunction f)

    val (axioms, _, functionTranslation) =
      Theory.toInternal(true,
        false,
        TermOrder.EMPTY extendPred predicates,
        functionEnc)

    (predicates,
      Conjunction.TRUE, /* axioms, */ Conjunction.TRUE,
      functionTranslation(mul))
  }

  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val functionalPredicates = predicates.toSet
  override val singleInstantiationPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)
  val triggerRelevantFunctions : Set[IFunction] = Set()

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
          val chosen = unprocessed.get
//println("next: " + chosen)
          val newPoly = active.reducePolynomial(passive, chosen)

          // If the new polynomial is reduced to zero, reiterate
          if (!newPoly.isZero) {
            val reducedActive  = active reduceBy newPoly
            val reducedPassive = passive reduceBy newPoly

            unprocessed add reducedActive
            unprocessed add reducedPassive

            passive add newPoly
          }

        } else if (!passive.isEmpty) {

          val newPoly = passive.get

          for (p <- active.polyIterator)
            if (newPoly.lt hasCommonVariables p.lt) {
              val spol = newPoly.spol(p)
              if (!spol.isZero)
                unprocessed add spol
            }

          active add newPoly

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
      implicit val _ = goal.order

//println("Groebner: " + goal.facts)

      // Fetch all predicates, if none nothing we can do
      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
      if (predicates.isEmpty)
        return List()

      if (Param.PROOF_CONSTRUCTION(goal.settings))
        throw new UnsupportedOperationException(
          "GroebnerMultiplication cannot generate proofs yet.\n" +
          "When using SimpleAPI, make sure that nonlinear formulae are\n" +
          "asserted only after calling setConstructProofs(true).")

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
    
          for (a <- predicates) {
            val p = atomToPolynomial(a)
    
            if (p.isZero)
              factsToRemove = a :: factsToRemove
            else
              basis add p
          }
 
          val gb = buchberger(basis)
          val simplified = gb.simplify

          oldGBSrc = predicatesList
          oldGBRes = Some((simplified, factsToRemove, monOrder))

          (simplified, factsToRemove, monOrder)
        }

      if (simplifiedGB.containsUnit)
        // we have an inconsistency
        return List(Plugin.AddFormula(Conjunction.TRUE))

      implicit val xMonOrder = monOrder

      //////////////////////////////////////////////////////////////////////////

      val removeFactsActions =
        if (factsToRemove.isEmpty)
          List()
        else
          List(Plugin.RemoveFacts(conj(factsToRemove)))

      // Translate this to a linear system

      def makeMap(polylist : List[Polynomial]) : List[Monomial] = {
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

      def makeMatrix(polylist : List[Polynomial]) : Array[Array[IdealInt]] = {
        var monomialMap = makeMap(polylist)
        val list =
          (for (p <- polylist)
          yield
            polyToRow(p, monomialMap)).toList

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

      // Did we find any linear formulas that can be propagated back
      val linearEq = simplifiedGB.toList
      if (!linearEq.isEmpty) {
        val map = makeMap(linearEq)
        val m = makeMatrix(linearEq)
        val gaussian = new Gaussian(m)

        val linearConj =
          conj(for (r <- gaussian.getRows;
                    poly = rowToPolynomial(map, r);
                    if (poly.isLinear))
               yield polynomialToAtom(poly))

        if (!linearConj.isTrue)
          return removeFactsActions ::: List(Plugin.AddFormula(linearConj.negate))
      }


      //////////////////////////////////////////////////////////////////////////
      // If Gröbner basis calculation does nothing
      // Lets try to do some interval propagation

      val preds = ((predicates.map(atomToPolynomial).toList).filter(
                     x => !x.isZero) ++ simplifiedGB.toSet).toList
      val ineqs = goal.facts.arithConj.inEqs
      val negeqs = goal.facts.arithConj.negativeEqs
      val intervalSet = new IntervalSet(
        preds,
        ineqs.map(lcToPolynomial).toList,
        negeqs.map(lcToPolynomial).toList)

      if (intervalSet.propagate)
        throw new Exception("Interval propagation error, abort!")

      val intervals = intervalSet.getIntervals

      var intervalAtoms = List[ap.terfor.inequalities.InEqConj]()
      for ((ct, i, (ul, uu, gu)) <- intervals) {
        // Generate inequalities according to intervals
        if (ul) {
          i.lower match {
            case IntervalNegInf =>
            case IntervalPosInf =>
              intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) =>
              intervalAtoms = (ct >= v) :: intervalAtoms
          }
        }

        if (uu) {
          i.upper match {
            case IntervalNegInf =>
              intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) =>
              intervalAtoms = (ct <= v) :: intervalAtoms
            case IntervalPosInf =>
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

      val crossInEqs =
        (for (a <- predicates.iterator;
              if (a(0).size == 1 && a(0).constants.size == 1 &&
                  a(1).size == 1 && a(1).constants.size == 1);
              i0 = intervalSet getTermInterval a(0).leadingTerm.asInstanceOf[ConstantTerm];
              (coeff0, bound0) <- enumBounds(i0 * a(0).leadingCoeff);
              i1 = intervalSet getTermInterval a(1).leadingTerm.asInstanceOf[ConstantTerm];
              (coeff1, bound1) <- enumBounds(i1 * a(1).leadingCoeff)) yield {
           (a(2) * coeff0 * coeff1) -
             (a(0) * coeff0 * bound1) -
             (a(1) * coeff1 * bound0) +
             (bound0 * bound1) >= 0
         }).toList

      //////////////////////////////////////////////////////////////////////////

      val allFormulas = goal reduceWithFacts conj(intervalAtoms ++ crossInEqs).negate
      if (!allFormulas.isFalse)
        return removeFactsActions ::: List(Plugin.AddFormula(allFormulas))

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
        implicit val _ = goal.order
        implicit val monOrder = new GrevlexOrdering(new StringOrdering)
        implicit val ctOrder = monOrder.termOrdering
  
//   println("Splitter: " + goal.facts)
  
        val preds = (predicates.map(atomToPolynomial).toList).filter(x => !x.isZero)
        val ineqs = goal.facts.arithConj.inEqs
        val negeqs = goal.facts.arithConj.negativeEqs
  
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
/*          def helper(list : List[(Set[ConstantTerm], Set[ConstantTerm])])
                    : Set[Set[ConstantTerm]] = {
            list match {
              case Nil => Set(Set()) : Set[Set[ConstantTerm]]
              case (xSet, ySet) :: rest => {
                  val recur = helper(rest)
                  val xRes = recur.map (x => x ++ xSet)
                  val yRes = recur.map (y => y ++ ySet)
                  (xRes ++ yRes)
                }
            }
          } */
  
          val predSet =
            for (p <- predicates)
            yield
              (p(0).constants, p(1).constants)
  
          val allConsts =
            (for ((_, consts) <- goal.bindingContext.constantSeq.iterator;
                  c <- consts.iterator)
             yield c).toSeq

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

//          helper(predSet)
        }
  
  
        def sphericalSplit(predicates : List[ap.terfor.preds.Atom],
                           intervalSet : IntervalSet)
                          : Iterator[(ap.terfor.Formula,
                                      ap.terfor.Formula, String)] =  {
          throw new Exception("sphericalSplit not enabled!")
        }
  
  
        /**
          * Splits intervals that ranges from -Inf to +Inf on zero
          */
  
        def infinitySplit(intervalSet : IntervalSet,
                          targetSet : Set[ConstantTerm])
                         : Iterator[(ap.terfor.Formula, ap.terfor.Formula, String)] = {
          (intervalSet.getAllIntervals.iterator.collect {
            case (c, i) if ((targetSet contains c) &&
                            i.lower == IntervalNegInf && i.upper == IntervalPosInf) => {
              val opt1 = (c >= 0)
              val opt2 = (c < 0)
              (opt1.negate, opt2.negate, "[-Inf, +Inf] split: " + opt1 + ", " + opt2)
            }
          })
        }
  
        /**
         * Finds any possible split by finding a lower (upper) bound b on any variable x
         * and the form the split x = b V x > b (x = b V x < b)
         */ 
        def desperateSplit(intervalSet : IntervalSet,
                           targetSet : Set[ConstantTerm])
                          : Iterator[(ap.terfor.Formula, ap.terfor.Formula, String)] = {
          val symbols = targetSet.toList.sortBy(_.name) // intervalSet.symbols.toList
  
          var alternatives = List[(ap.terfor.Formula, ap.terfor.Formula, String)]()
  
          (for (x <- symbols)
          yield {
            (PresburgerTools.lowerBound(l(x), goal.facts.arithConj),
              PresburgerTools.lowerBound(l(-x), goal.facts.arithConj)) match {
              case (Some(ll), Some(ul)) if (ll < ul) => {
                val opt1 = (x === ll)
                val opt2 = (x > ll)
                alternatives = (opt1.negate, opt2.negate,
                                "LowerBound split: " + opt1 + ", " + opt2) :: alternatives
              }
              case (Some(ll), _) => {
                val opt1 = (x === ll)
                val opt2 = (x > ll)
                alternatives = (opt1.negate, opt2.negate,
                                "LowerBound split: " + opt1 + ", " + opt2) :: alternatives
              }
              case (_, Some(ul)) => {
                val opt1 = (x === -ul)
                val opt2 = (x < -ul)
  
                alternatives = (opt1.negate, opt2.negate,
                                "UpperBound split: " + opt1 + ", " + opt2 ) :: alternatives
              }
              case (None, None) =>
            }
          })
  
          alternatives.iterator
        }
  
  
  
        /**
         * Takes negative equations (i.e. x+y+... != 0) and splits them around zero
         */
        def negeqSplit(negeqs : ap.terfor.equations.NegEquationConj)
                      : Iterator[(ap.terfor.Formula, ap.terfor.Formula, String)] = {
          var alternatives = List[(ap.terfor.Formula, ap.terfor.Formula, String)]()
  
          for (negeq <- negeqs.toList) {
            val negeq = negeqs.head
            val opt1 = (negeq > 0)
            val opt2 = (negeq < 0)
  
            val opt1reduced = goal reduceWithFacts(opt1.negate)
            val opt2reduced = goal reduceWithFacts(opt2.negate)
  
            if (!opt1reduced.isFalse && !opt2reduced.isFalse)
              alternatives = (opt1.negate, opt2.negate,
                              "Negeq split on: " + negeq) :: alternatives
          }
  
          alternatives.iterator
        }
  
        /**
         * Utilizes any gaps in an interval (i.e. x = [lb, -a] U [a, ub]) 
         *  and branches into two (i.e. x <= -a V x >= a)
         *
         */
        def gapSplit(intervalSet : IntervalSet,
                     targetSet : Set[ConstantTerm])
                    : Iterator[(ap.terfor.Formula, ap.terfor.Formula, String)] = {
          val gaps = intervalSet.getGaps
          (for ((term, interval) <- gaps.iterator;
                if (targetSet contains term))
          yield {
            val opt1 = (term < interval.gap.get._1)
            val opt2 = (term > interval.gap.get._2)
            (opt1.negate, opt2.negate, "Gap split on " + term + " using " + interval)
          })
        }
  
  
        /**
          * 
          * END OF SPLITTING STRATEGIES
          * 
          */
  
  
        // Converts a split alternative to a Plugin.SplitGoal
        def doSplit(splitparams : (ap.terfor.Formula, ap.terfor.Formula, String))
                   : List[Plugin.Action] = {
          val (opt1, opt2, msg) = splitparams
          val opt1act = Conjunction.conj(opt1, goal.order)
          val opt2act = Conjunction.conj(opt2, goal.order)
          val splitgoal =
            Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)),
                                  List(Plugin.AddFormula(opt2act))))
          List(splitgoal)
        }
  
        val intervalSet = new IntervalSet(
          preds,
          ineqs.map(lcToPolynomial).toList,
          negeqs.map(lcToPolynomial).toList)
  
        intervalSet.propagate
        if (!intervalSet.getInconsistency.isEmpty) {
          return List(Plugin.AddFormula(Conjunction.TRUE))
        }

        // Let the target set be the smallest set such that all
        // predicates are made linear
        val targetSet = linearizers(predicates.toList).toList
                           .sortWith((s1, s2) => s1.size > s2.size).head
  
        val alternatives = negeqSplit(negeqs) ++ gapSplit(intervalSet, targetSet) ++ 
          (Param.NONLINEAR_SPLITTING(goal.settings) match {
            case Param.NonLinearSplitting.Sign =>
              infinitySplit(intervalSet, targetSet) ++
              desperateSplit(intervalSet, targetSet)
            case Param.NonLinearSplitting.Spherical =>
              sphericalSplit(predicates.toList, intervalSet)
          })
  
        if (!alternatives.isEmpty) {
          val s = alternatives.next
//          println("Splitting: " + s)
          return doSplit(s)
        }
  
        val retList = handleGoalAux(goal, true)
        if (retList.isEmpty)
          throw new Exception("ERROR: No splitting alternatives found: " +
                              intervalSet)
  
        retList
      }
    }
  })


  TheoryRegistry register this

  override def toString = "GroebnerMultiplication"
}
