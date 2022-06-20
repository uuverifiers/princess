/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2022 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.theories.nia

import ap._
import ap.parser._
import ap.theories._
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.terfor.{TermOrder, ConstantTerm, OneTerm, Formula, ComputationLogger,
                  Term}
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPluginFactory, IdentityReducerPlugin,
                               ReducerPlugin}
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.basetypes.IdealInt
import ap.util.{Timeout, Seqs, Debug, LRUCache, IdealRange}

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer, LinkedHashSet}


/**
 * Implementation of a theory of non-linear integer arithmetic.
 * Currently the theory does Groebner basis calculation followed
 * by interval propagation.
 */
object GroebnerMultiplication extends MulTheory {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  protected[nia] val debug = false
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  // Some options for splitting

  // Below this threshold, split intervals x in [a, b] into the individual cases
  // x = a, x = a+1, ..., x = b
  val DISCRETE_SPLITTING_LIMIT = 20

  // Randomly pick the next variable to split over
  val RANDOMISE_VARIABLE_ORDER = true

  // Randomise the order in which the splitting cases are handled
  val RANDOMISE_CASES          = false

  private val AC = Debug.AC_NIA

  val mul        = new IFunction("mul", 2, true, false)
  val _mul       = new Predicate("mul", 3)
  val functions  = List(mul)
  val predicates = List(_mul)

  val axioms         = Conjunction.TRUE
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig : Signature.PredicateMatchConfig =
    Map(_mul -> Signature.PredicateMatchStatus.None)
  val functionalPredicates = predicates.toSet
  override val singleInstantiationPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)
  val triggerRelevantFunctions : Set[IFunction] = Set()

  override def isSoundForSat(
                  theories : Seq[Theory],
                  config : Theory.SatSoundnessConfig.Value) : Boolean = true

  //////////////////////////////////////////////////////////////////////////////
  /**
   * Conversion functions
   */

  protected[nia] def genMonomialOrder(predicates : Seq[Atom],
                                      baseOrder : TermOrder)
                                    : MonomialOrdering = {
    val inputConsts = new MHashSet[ConstantTerm]

    // We first compute the "defined" symbols, which are the symbols
    // occurring in the terms c of multiplication atoms mul(a, b, c).

    // Consider the symbols in the terms a, b as "input symbols"
    for (a <- predicates) {
      inputConsts ++= a(0).constants
      inputConsts ++= a(1).constants
    }

    // Remove the constants that were generated internally
    // TODO: this should not be done based on the name
    for (a <- predicates.iterator)
      for (x <- a(2).constants.iterator)
        if ((x.name startsWith "all") ||
            (x.name startsWith "ex") ||
            (x.name startsWith "sc"))
          inputConsts -= x

    // Fix-point computation to find the defined constants in the c terms
    val definedConsts = new LinkedHashSet[ConstantTerm]
    val remainingPreds = new LinkedHashSet[Atom]

    for (a <- predicates)
      if (!a(2).isConstant)
        remainingPreds += a

    var cont = true
    while (cont) {
      cont = false

      val predIt = remainingPreds.iterator
      while (!cont && predIt.hasNext) {
        val a = predIt.next
        val lhsDefined =
          (a(0).constants.iterator ++ a(1).constants.iterator) forall inputConsts

        if (lhsDefined) {
          remainingPreds -= a
          val x = a(2).leadingTerm.asInstanceOf[ConstantTerm]
          inputConsts += x
          definedConsts += x
          cont = true // exit the inner loop, continue in the outer loop
        }
      }
    }

    val orderList = definedConsts.toIndexedSeq
    new PartitionOrdering(orderList,
                          new GrevlexOrdering(baseOrder.constOrdering))
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Reducer extends ReducerPlugin {
    object factory extends ReducerPluginFactory {
      def apply(conj : Conjunction, order : TermOrder) = Reducer
    }
    
    def passQuantifiers(num : Int) = this

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def reduce(predConj : PredConj,
               baseReducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult =
      if (logger.isLogging) {
        ReducerPlugin.UnchangedResult
      } else {
        implicit val order = predConj.order
        ReducerPlugin.rewritePreds(predConj, List(_mul), order) {
          a =>
            if (a(0).isConstant)
              a(0).constant * a(1) === a(2)
            else if (a(1).isConstant)
              a(1).constant * a(0) === a(2)
            else
              a
        }
      }

    def finalReduce(conj : Conjunction) = conj
  }

  override val reducerPlugin : ReducerPluginFactory = Reducer.factory

  //////////////////////////////////////////////////////////////////////////////

  def plugin = Some(new Plugin {

    private val gbCache =
      new LRUCache[(Seq[Atom], TermOrder), (Basis, Seq[Atom], MonomialOrdering)](5)

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val negPreds = goal.facts.predConj.negativeLitsWithPred(_mul)

      if (!negPreds.isEmpty) {
        // replace negated predicates with positive predicates

        implicit val order = goal.order

        (for (a <- negPreds) yield {
          val axiom =
            exists(Atom(_mul, a.init ++ List(l(v(0))), order) &
                   (v(0) =/= a.last))
          Plugin.AddAxiom(List(!conj(a)), axiom, GroebnerMultiplication.this)
        }) ++ List(Plugin.RemoveFacts(conj(for (a <- negPreds) yield !conj(a))))

      } else {
      
        handleGoalAux(goal, false)

      }
    }

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
      def termToLc(t : CoeffMonomial) : LinearCombination = {
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

    ////////////////////////////////////////////////////////////////////////////

    def handleGoalAux(goal : Goal,
                      calledFromSplitter : Boolean) : Seq[Plugin.Action] = {
      implicit val order = goal.order

      // Fetch all predicates, if none nothing we can do
      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
      if (predicates.isEmpty)
        return List()

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      printNIAgoal("Calling theory solver: NIA", goal)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val inequalities = goal.facts.arithConj.inEqs
      val disequalities = goal.facts.arithConj.negativeEqs

      val ineqOffset = predicates.size
      val ineqInfsOffset = ineqOffset + inequalities.size
      val negeqOffset = ineqInfsOffset + inequalities.allGeqZeroInfs.size

      def label2Assumptions(l : BitSet) : Seq[Formula] =
        for (ind <- l.toSeq) yield {
          if (ind < ineqOffset)
            predicates(ind)
          else if (ind < ineqInfsOffset)
            InEqConj(inequalities(ind - ineqOffset), order)
          else if (ind < negeqOffset)
            InEqConj(inequalities.allGeqZeroInfs(ind - ineqInfsOffset), order)
          else
            NegEquationConj(disequalities(ind - negeqOffset), order)
        }

      val (simplifiedGB, factsToRemove, monOrder) = gbCache((predicates.toList,
                                                             order)) {
          // Create a monomial ordering
          implicit val monOrder = genMonomialOrder(predicates, order)

          val basis = new Basis
          var factsToRemove = List[ap.terfor.preds.Atom]()
    
          for ((a, index) <- predicates.iterator.zipWithIndex) {
            val p = Polynomial fromMulAtomGen a
    
            if (p.isZero)
              factsToRemove = a :: factsToRemove
            else
              basis.add(p, BitSet(index))
          }
 
          val gb = buchberger(basis)
          val simplified = gb.simplify

          (simplified, factsToRemove, monOrder)
        }

      for (p <- simplifiedGB.containsUnit) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug)
          println("GB found inconsistency: " +
                  label2Assumptions(simplifiedGB labelFor p))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return List(Plugin.CloseByAxiom(
                             label2Assumptions(simplifiedGB labelFor p),
                             GroebnerMultiplication.this))
      }

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

      def makeMatrix(polylist : Seq[Polynomial]) : Vector[Vector[IdealInt]] = {
        var monomialMap = makeMap(polylist)
        (for (p <- polylist) yield polyToRow(p, monomialMap).toVector).toVector
      }

      def rowToPolynomial(map : List[Monomial], row : Array[IdealInt]) = {
        var retPoly = Polynomial(List())
        for (i <- 0 until row.length;
          if (!row(i).isZero))
          retPoly += new CoeffMonomial(row(i), map(i))

        retPoly
      }

      // Did we find any linear formulas that can be propagated back?
      val linearEq = simplifiedGB.toArray
      if (!linearEq.isEmpty) {
        if (linearEq forall (_.isLinear)) {

          val actions =
            (for (p <- linearEq.iterator;
                  c = polynomialToAtom(p) /* ;
                  if !(goal reduceWithFacts c).isTrue */)
             yield Plugin.AddAxiom(label2Assumptions(simplifiedGB labelFor p),
                                   c, GroebnerMultiplication.this)).toList
          
          if (!actions.isEmpty) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printActions("GB discovered implied linear formulas", actions)
            //-END-ASSERTION-///////////////////////////////////////////////////
            return removeFactsActions ::: actions
          }

        } else if (linearEq.size > 1) {

          val map = makeMap(linearEq)
          val m = makeMatrix(linearEq)

          val implications =
            (for ((r, preLabel) <- Gaussian(m).iterator;
                  poly = rowToPolynomial(map, r);
                  if (poly.isLinear))
             yield (polynomialToAtom(poly),
                    BitSet() ++
                      (for (ind <- preLabel.iterator;
                            ind2 <- simplifiedGB labelFor linearEq(ind))
                       yield ind2))).toList

          if (!implications.isEmpty) {
            val actions =
              for ((eq, label) <- implications)
              yield Plugin.AddAxiom(label2Assumptions(label), eq,
                                    GroebnerMultiplication.this)
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printActions("GB discovered implied linear formulas", actions)
            //-END-ASSERTION-///////////////////////////////////////////////////
            return removeFactsActions ::: actions
          }
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Check if any of the polynomials have common factors, as an
      // approximation of factorisation

      {
        var actions : List[Plugin.Action] = List()

        for (p <- linearEq)
          if (!p.isZero) {
            val factor = p.commonFactor
            if (!factor.isEmpty) {
              val assumptions =
                label2Assumptions(simplifiedGB labelFor p)
              val remainingPoly =
                p / CoeffMonomial(IdealInt.ONE, factor)
              val factorisation =
                disjFor(List(polynomialToAtom(remainingPoly)) ++
                        (for (v <- factor.variables) yield (v === 0)))
              actions = Plugin.AddAxiom(assumptions,
                                        factorisation,
                                        GroebnerMultiplication.this) :: actions
            }
          }

        if (!actions.isEmpty) {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          printActions("GB discovered factorisation of a polynomial", actions)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          return removeFactsActions ::: actions
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // If Gröbner basis calculation does nothing
      // Lets try to do some interval propagation

      val propagator =
        IntervalPropagator(goal, monOrder, simplifiedGB,
                           alwaysCreateIntervalSet = true)
      val Some(intervalSet) = propagator.intervalSet

      val intActions =
        filterActions(intervals2Actions(
                                intervalSet, predicates,
                                goal, label2Assumptions _) ++
//                      crossMult(intervalSet, predicates,
//                                goal, label2Assumptions _) ++
                      filterSubsumedActions(crossMult2(predicates, goal),
                                            goal, intervalSet),
                      order)

      if (!intActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        printActions("ICP/cross-multiplication discovered inequalities",
                     intActions)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return removeFactsActions ++ intActions
      }

      // Do splitting
      if (calledFromSplitter)
        return List()

      goalState(goal) match {
        case Plugin.GoalState.Final =>
          // Split directly!
          removeFactsActions ::: (Splitter handleGoal goal).toList
        case _ =>
          val scheduleAction = Plugin.ScheduleTask(Splitter, 10)
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

      (goal reduceWithFacts conj(
         for (Plugin.AddAxiom(_, f, _) <-
                intervals2Actions(intervalSet, predicates,
                                  goal, l => List()).iterator)
         yield f)).negate
    }

    private def intervals2Actions(intervalSet : IntervalSet,
                                  predicates : IndexedSeq[Atom],
                                  goal : Goal,
                                  label2Assumptions : BitSet => Seq[Formula])
                                 : Seq[Plugin.Action] = {
      implicit val order = goal.order

      val intervalAtoms = new ArrayBuffer[(ArithConj, BitSet)]

      for ((ct, i, (ul, uu, _), (l1, l2, _)) <- intervalSet.getIntervals) {

        if ((ul || uu) && i.lower == i.upper) {
          i.lower match {
            case IntervalVal(v) => intervalAtoms += ((ct === v, l1 | l2))
            case _ => // nothing
          }
        } else {
          // Generate inequalities according to intervals
          if (ul) {
            i.lower match {
              case IntervalNegInf =>
              case IntervalPosInf => {
                intervalAtoms += ((ct > 0, l1))
                intervalAtoms += ((ct < 0, l1))
              }
              case IntervalVal(v) =>
                intervalAtoms += ((ct >= v, l1))
            }
          }

          if (uu) {
            i.upper match {
              case IntervalNegInf => {
                intervalAtoms += ((ct > 0, l2))
                intervalAtoms += ((ct < 0, l2))
              }
              case IntervalVal(v) =>
                intervalAtoms += ((ct <= v, l2))
              case IntervalPosInf =>
            }
          }
        }
      }

      (for ((f, label) <- intervalAtoms.iterator;
            if !(goal reduceWithFacts f).isTrue)
       yield (Plugin.AddAxiom(label2Assumptions(label), conj(f),
                              GroebnerMultiplication.this))).toList
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Generate linear approximations of quadratic terms using
     * cross-multiplication. This version only considers inequalities
     * with exactly one constant symbol.
     */
    private def crossMult(intervalSet : IntervalSet,
                          predicates : IndexedSeq[Atom],
                          goal : Goal,
                          label2Assumptions : BitSet => Seq[Formula])
                         : Seq[Plugin.Action] = {
      implicit val order = goal.order

      def enumBounds(i : Interval,
                     ll : BitSet, lu : BitSet) 
                   : Iterator[(IdealInt, IdealInt, BitSet)] =
        (i.lower match {
           case IntervalVal(v) => Iterator single ((IdealInt.ONE, v, ll))
           case _ => Iterator.empty
         }) ++
        (i.upper match {
           case IntervalVal(v) => Iterator single ((IdealInt.MINUS_ONE, -v, lu))
           case _ => Iterator.empty
         })

      val crossInEqs : Iterator[(ArithConj, BitSet)] =
        for ((a, predN) <- predicates.iterator.zipWithIndex;
             if (a(0).size == 1 && a(0).constants.size == 1 &&
                 a(1).size == 1 && a(1).constants.size == 1);
             ca0 = a(0).leadingTerm.asInstanceOf[ConstantTerm];
             ca1 = a(1).leadingTerm.asInstanceOf[ConstantTerm];
             (i0, (l0l, l0u, _)) = intervalSet getLabelledTermInterval ca0;
             (i1, (l1l, l1u, _)) = intervalSet getLabelledTermInterval ca1;
             (coeff0, bound0, l0) <- enumBounds(i0 * a(0).leadingCoeff, l0l, l0u);
             (coeff1, bound1, l1) <- enumBounds(i1 * a(1).leadingCoeff, l1l, l1u);
             ineq = (a(2) * coeff0 * coeff1) -
                    (a(0) * coeff0 * bound1) -
                    (a(1) * coeff1 * bound0) +
                    (bound0 * bound1) >= 0;
             // heuristic condition to
             // avoid looping by introducing steeper and steeper inequalities
             if (a(0) != a(1) ||
                 !(goal.facts.arithConj.inEqs exists { lc =>
                     lc.constants == ineq.constants &&
                     lc.leadingCoeff.signum == ineq.head.leadingCoeff.signum
                   })
                 )) yield {
          (ineq, (l0 | l1) + predN)
        }

      (for ((f, label) <- crossInEqs;
            if !(goal reduceWithFacts f).isTrue)
       yield (Plugin.AddAxiom(label2Assumptions(label), conj(f),
                              GroebnerMultiplication.this))).toList
    }

    ////////////////////////////////////////////////////////////////////////////

    private val CROSS_COEFF_BOUND = IdealInt(5)

    private def lcWithSmallCoeffs(lc : LinearCombination) = lc forall {
      case (_, OneTerm) => true
      case (coeff, _) => coeff.abs <= CROSS_COEFF_BOUND
    }

    /**
     * Generate linear approximations of quadratic terms using
     * cross-multiplication. This version considers all inequalities
     * with coefficients bounded by <code>CROSS_COEFF_BOUND</code>
     * (to avoid looping behaviour), provided that the result of
     * cross-multiplication can be expressed as a linear inequality
     * using just the product terms that already exist in a goal.
     */
    private def crossMult2(predicates : IndexedSeq[Atom], goal : Goal)
                          : Seq[Plugin.Action] = {
      implicit val order = goal.order

      val multMapping : Map[(ConstantTerm, ConstantTerm),
                            (LinearCombination, Atom)] =
        (for (a <- predicates.iterator;
              if a(0).constants.size == 1 && a(0).leadingCoeff.isUnit &&
                 a(1).constants.size == 1 && a(1).leadingCoeff.isUnit;
              c0 = a(0).leadingTerm.asInstanceOf[ConstantTerm];
              c1 = a(1).leadingTerm.asInstanceOf[ConstantTerm];
              // (c1 x1 + d1) * (c2 x2 + d2) = t
              // c1 c2 x1 x2 + c1 d2 x1 + c2 d1 x2 + d1 d2 = t
              // x1 x2 = (t - c1 d2 x1 - c2 d1 x2 - d1 d2) / c1 c2
              val fact = a(0).leadingCoeff * a(1).leadingCoeff;
              rhs =
                LinearCombination(List(
                  (fact, a(2)),
                  (- a(0).leadingCoeff * a(1).constant * fact, c0),
                  (- a(1).leadingCoeff * a(0).constant * fact, c1),
                  (- a(0).constant * a(1).constant * fact, OneTerm)),
                  order);
              key <- Seqs.doubleIterator((c0, c1), (c1, c0))) yield {
           (key, (rhs, a))
         }).toMap

      val mappedTerms =
        (for (((c, d), _) <- multMapping.iterator;
              x <- Seqs.doubleIterator(c, d))
         yield x).toSet

      val ineqs =
        (for (lc <- goal.facts.arithConj.inEqs.iterator ++
                    goal.facts.arithConj.inEqs.allGeqZeroInfs.iterator;
              if (lc.constants subsetOf mappedTerms) &&
                 lcWithSmallCoeffs(lc))
         yield lc).toIndexedSeq

      val crossLC = new ArrayBuffer[(IdealInt, Term)]
      val assumptions = new ArrayBuffer[Formula]

      val res = new ArrayBuffer[Plugin.Action]

      for (ind1  <- 0 until ineqs.size;
           ineq1 = ineqs(ind1);
           n1    = ineq1.size;
           ind2  <- ind1 until ineqs.size;
           ineq2 = ineqs(ind2)) {
        crossLC.clear
        assumptions.clear

        val n2 = ineq2.size

        var cont = true
        var i1 = 0
        while (cont && i1 < n1) {
          (ineq1 getTerm i1) match {
            case OneTerm =>
              crossLC += ((ineq1 getCoeff i1, ineq2))
            case c1 : ConstantTerm => {
              val coeff1 = ineq1 getCoeff i1
              
              var i2 = 0
              while (cont && i2 < n2) {
                (ineq2 getTerm i2) match {
                  case OneTerm =>
                    crossLC += ((coeff1 * (ineq2 getCoeff i2), c1))
                  case c2 : ConstantTerm =>
                    (multMapping get (c1, c2)) match {
                      case Some((rhs, atom)) => {
                        crossLC += ((coeff1 * (ineq2 getCoeff i2), rhs))
                        assumptions += atom
                      }
                      case None =>
                        cont = false
                    }
                }
            
                i2 = i2 + 1
              }
            }
          }

          i1 = i1 + 1
        }

        if (cont) {
          val newInEq = InEqConj(LinearCombination(crossLC, order), order)

          if (!(goal reduceWithFacts newInEq).isTrue) {
            assumptions += InEqConj(ineq1, order)
            assumptions += InEqConj(ineq2, order)

            res += Plugin.AddAxiom(assumptions.toList.distinct, newInEq,
                                   GroebnerMultiplication.this)
          }
        }
      }

      res
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Check whether <code>ineq1 >= 0</code> implies <code>ineq2 >= 0</code>,
     * given the ranges of variables provided.
     */
    private def ineqImplies(ineq1 : LinearCombination,
                            ineq2 : LinearCombination,
                            intervalSet : IntervalSet) : Boolean =
      ineq1.constants == ineq2.constants && {
        var diff = ineq2.constant - ineq1.constant

        val n = ineq1.size min ineq2.size
        var ind = 0
        while (ind < n) {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, (ineq1 getTerm ind) == (ineq2 getTerm ind))
          //-END-ASSERTION-/////////////////////////////////////////////////////

           (ineq1 getTerm ind) match {
             case c : ConstantTerm => {
               val coeffDiff = (ineq2 getCoeff ind) - (ineq1 getCoeff ind)
               coeffDiff.signum match {
                 case 0 =>
                   // nothing
                 case sig =>
                   (intervalSet getTermIntervalOption c) match {
                     case Some(interval) =>
                       if (sig > 0) {
                         interval.lower match {
                           case IntervalVal(v) =>
                             diff = diff + (coeffDiff * v)
                           case _ =>
                             return false
                         }
                       } else {
                         interval.upper match {
                           case IntervalVal(v) =>
                             diff = diff + (coeffDiff * v)
                           case _ =>
                             return false
                         }
                       }
                     case None =>
                       return false
                   }
               }
             }
             case _ =>
               // nothing
           }

          ind = ind + 1
        }

        diff.signum >= 0
      }

    /**
     * Check whether <code>ineq1 >= 0</code> implies <code>ineq2 >= 0</code>
     * talk about the same variables, and have coefficients with the same
     * sign.
     */
    private def similarIneqs(ineq1 : LinearCombination,
                             ineq2 : LinearCombination) : Boolean =
      (ineq1.iterator zip ineq2.iterator) forall {
        case ((coeff1, c1 : ConstantTerm), (coeff2, c2 : ConstantTerm))
          if c1 == c2 => coeff1.signum == coeff2.signum
        case ((_, OneTerm), (_, OneTerm)) =>
          true
        case _ =>
          false
      }

    private def filterSubsumedActions(actions : Seq[Plugin.Action],
                                      goal : Goal,
                                      intervalSet : IntervalSet)
                                     : Seq[Plugin.Action] = {
      implicit val order = goal.order
      val ineqs = goal.facts.arithConj.inEqs

      val res = new ArrayBuffer[Plugin.Action]

      for (act <- actions) act match {
        case Plugin.AddAxiom(_, c, _)
          if c.isArithLiteral && c.arithConj.inEqs.size == 1 &&
             c.constants.size > 1 => {

          val ineq = c.arithConj.inEqs.head
          if (ineqs.findInEqsWithLeadingTerm(ineq.leadingTerm, true) exists {
                lc => ineqImplies(lc, ineq, intervalSet) ||
                      (!lcWithSmallCoeffs(ineq) && similarIneqs(lc, ineq))
              }) {
            // forward subsumption:
            // this inequality is implied by some inequalities that already
            // exists in the goal, skip it
            // or
            // the inequality contains large coefficients, and is similar
            // to some other inequality that we already know (-> heuristic
            // to prevent looping)
          } else {
            res += act

            // check possible backward subsumptions
            val toElim =
              (ineqs.findInEqsWithLeadingTerm(ineq.leadingTerm) filter {
                 lc => ineqImplies(ineq, lc, intervalSet) }) >= 0
            if (!toElim.isTrue)
              res += Plugin.RemoveFacts(toElim)
          }
        }
        case _ =>
          res += act
      }

      res
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Splitter handles the splitting when no new information can be deduced
     */
    object Splitter extends TheoryProcedure  {
      def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {

        // Compute a minimal set of variables that in enough to linearise all
        // multiplication atoms
        val MINIMAL_SPLITTING_SET =
          Param.NONLINEAR_SPLITTING(goal.settings) match {
            case Param.NonLinearSplitting.SignMinimal => true
            case _                                    => false
          }
  
        // Extract all predicates
        val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
  
        if (predicates.isEmpty)
          return List()
  
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        printNIAgoal("Calling NIA splitter", goal)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        implicit val order = goal.order
        implicit val monOrder = new GrevlexOrdering(order.constOrdering)
        implicit val ctOrder = monOrder.termOrdering
  
        val preds =
          (for ((a, n) <- predicates.iterator.zipWithIndex;
                poly = Polynomial fromMulAtom a;
                if !poly.isZero)
           yield (poly, BitSet(n))).toList

        val inequalities = goal.facts.arithConj.inEqs
        val disequalities = goal.facts.arithConj.negativeEqs
        val equalities = goal.facts.arithConj.positiveEqs

        val ineqOffset = predicates.size
        val ineqInfsOffset = ineqOffset + inequalities.size
        val negeqOffset = ineqInfsOffset + inequalities.allGeqZeroInfs.size
        val eqOffset = negeqOffset + disequalities.size
  
        val ineqPolys, negeqPolys = new ArrayBuffer[(Polynomial, BitSet)]
        val basicBounds = new ArrayBuffer[(LinearCombination, BitSet)]

        def addFacts(conj : ArithConj) : Unit = {
          import Polynomial.{fromLinearCombination => fromLC}

          for ((lc, n) <- conj.inEqs.iterator.zipWithIndex;
               if lc.constants.size > 1)
            ineqPolys += ((fromLC(lc), BitSet(n + ineqOffset)))
          for ((lc, n) <- conj.positiveEqs.iterator.zipWithIndex) {
            ineqPolys += ((fromLC(lc), BitSet(n + eqOffset)))
            ineqPolys += ((fromLC(-lc), BitSet(n + eqOffset)))
          }
          for ((lc, n) <- conj.negativeEqs.iterator.zipWithIndex)
            negeqPolys += ((fromLC(lc), BitSet(n + negeqOffset)))
          for ((lc, n) <- conj.inEqs.iterator.zipWithIndex;
               if lc.constants.size == 1)
            basicBounds += ((lc, BitSet(n + ineqOffset)))
          for ((lc, n) <- conj.inEqs.allGeqZeroInfs.iterator.zipWithIndex;
               if lc.constants.size == 1)
            basicBounds += ((lc, BitSet(n + ineqInfsOffset)))
        }

        def label2Assumptions(l : BitSet) : Seq[Formula] =
          for (ind <- l.toSeq) yield {
            if (ind < ineqOffset)
              predicates(ind)
            else if (ind < ineqInfsOffset)
              InEqConj(inequalities(ind - ineqOffset), order)
            else if (ind < negeqOffset)
              InEqConj(inequalities.allGeqZeroInfs(ind - ineqInfsOffset), order)
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
  
        def linearizers(predicates : List[ap.terfor.preds.Atom],
                        intervalSet : IntervalSet) : Set[ConstantTerm] = {
  
          // Given the List [({x11, x12, ...}, {y11, y12, ...}), ({x21, ....]
          // returns {{x1*, x2*, x3* ...xn*}, {x1*, x2*, ... yn*}, ..., {y1*, y2*, ... yn*}}
  
          val predSet =
            for (p <- predicates) yield (p(0).constants, p(1).constants)
          val relevantConsts =
            (for ((s, t) <- predSet.iterator; c <- s.iterator ++ t.iterator)
             yield c).toSet

          val allConsts = relevantConsts.toVector sortWith {
            case (c, d) => {
              val cInt = intervalSet getTermInterval c
              val cBoundNum =
                (if (cInt.lower == IntervalNegInf) 0 else 1) +
                (if (cInt.upper == IntervalPosInf) 0 else 1)

              val dInt = intervalSet getTermInterval d
              val dBoundNum =
                (if (dInt.lower == IntervalNegInf) 0 else 1) +
                (if (dInt.upper == IntervalPosInf) 0 else 1)

              cBoundNum < dBoundNum ||
              (cBoundNum == dBoundNum) && order.compare(c, d) < 0
            }
          }

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

          allConstsSet.toSet
        }
  
        /**
          * Splits intervals that ranges from -Inf to +Inf on zero
          */
  
        def infinitySplit(intervalSet : IntervalSet,
                          targetSet : Set[ConstantTerm])
                         : Iterator[(Seq[ArithConj], String, BitSet,
                                     Seq[Plugin.Action])] = {
          (intervalSet.getAllIntervals.iterator.collect {
            case (c, i, label) if ((targetSet contains c) &&
                                   i.lower == IntervalNegInf &&
                                   i.upper == IntervalPosInf) => {
              val opt1 = (c >= 0)
              val opt2 = (c < 0)
              (List(opt1.negate, opt2.negate),
               "[-Inf, +Inf] split: " + opt1 + ", " + opt2,
               BitSet(),
               splitTermAt(c, IdealInt.ZERO))
            }
          })
        }
  
        def splitTermAt(x : ConstantTerm, mid : IdealInt,
                        swap : Boolean = false) : Seq[Plugin.Action] =
          if (swap)
            List(Plugin.CutSplit(x > mid, List(), List()))
          else
            List(Plugin.CutSplit(x <= mid, List(), List()))

        /**
         * Finds a possible split of x in [a, b] into the individual cases
         * x = a, x = a + 1, ..., x = b
         */ 
        def discreteSplit(intervalSet : IntervalSet,
                          targetSet : Seq[ConstantTerm])
                        : Iterator[(Seq[ArithConj], String, BitSet,
                                    Seq[Plugin.Action])] = {
          val ac = goal.facts.arithConj

          for (x <- targetSet.iterator;
               res <- (intervalSet getLabelledTermInterval x) match {
                 case (Interval(IntervalVal(ll),
                                IntervalVal(ul), _), (label1, label2, _))
                     if (ll < ul && ll >= ul - DISCRETE_SPLITTING_LIMIT) => {
                   val options =
                     for (n <- IdealRange(ll, ul + 1))
                     yield ArithConj.conj(x === n, order).negate
                   Iterator single ((options,
                                     "Discrete split: " + x + " in [" +
                                       ll + ", " + ul + "]",
                                     label1 | label2, null))
                 }
                 case _ =>
                   Iterator.empty
               })
          yield res
        }

        /**
         * Splitting of intervals in the middle
         */ 
        def binarySplit(intervalSet : IntervalSet,
                        targetSet : Seq[ConstantTerm])
                      : Iterator[(Seq[ArithConj], String, BitSet,
                                  Seq[Plugin.Action])] = {
          val ac = goal.facts.arithConj

          for (x <- targetSet.iterator;
               res <- (intervalSet getLabelledTermInterval x) match {
                 case (Interval(IntervalVal(ll),
                                IntervalVal(ul), _), _)
                     if (ll < ul) => {
                   val mid = (ll + ul) / 2
                   val opt1 = ArithConj.conj(x <= mid, order)
                   val opt2 = ArithConj.conj(x > mid, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                     "Interval split: " + x + " in [" +
                                       ll + ", " + ul + "] at " + mid,
                                     BitSet(), splitTermAt(x, mid)))
                 }
                 case (Interval(IntervalVal(ll), IntervalPosInf, _), _)
                     if ll.signum > 0 => {
                   val mid = 2*ll
                   val opt1 = ArithConj.conj(x <= mid, order)
                   val opt2 = ArithConj.conj(x > mid, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                     "Exp lowerbound split: " +
                                        opt1 + ", " + opt2,
                                     BitSet(), splitTermAt(x, mid)))
                 }
                 case (Interval(IntervalVal(ll), IntervalPosInf, _),
                       (label, _, _))
                     if ll >= IdealInt.MINUS_ONE => {
                   val opt1 = ArithConj.conj(x === ll, order)
                   val opt2 = ArithConj.conj(x > ll, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                     "LowerBound split: " + opt1 + ", " + opt2,
                                     label, null))
                 }
                 case (Interval(IntervalNegInf, IntervalVal(ul), _), _)
                     if ul.signum < 0 => {
                   val mid = 2*ul
                   val opt1 = ArithConj.conj(x > mid, order)
                   val opt2 = ArithConj.conj(x <= mid, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                     "Exp upperbound split: " +
                                        opt1 + ", " + opt2,
                                     BitSet(), splitTermAt(x, mid, true)))
                 }
                 case (Interval(IntervalNegInf, IntervalVal(ul), _),
                       (_, label, _))
                      if ul <= IdealInt.ONE => {
                   val opt1 = ArithConj.conj(x === ul, order)
                   val opt2 = ArithConj.conj(x < ul, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                     "UpperBound split: " + opt1 + ", " + opt2,
                                     label, null))
                 }
                 case (Interval(IntervalVal(_), IntervalPosInf, _), _) |
                      (Interval(IntervalNegInf, IntervalVal(_), _), _) => {
                   val opt1 = ArithConj.conj(x >= 0, order)
                   val opt2 = ArithConj.conj(x < 0, order)
                   Iterator single ((List(opt1.negate, opt2.negate),
                                    "[-Inf, +Inf] split: " + opt1 + ", " + opt2,
                                    BitSet(),
                                    splitTermAt(x, IdealInt.ZERO)))
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
                      : Iterator[(Seq[ArithConj], String, BitSet,
                                 Seq[Plugin.Action])] =
          for (negeq <- negeqs.iterator;
               if (negeq.constants.size == 1);
               c = negeq.constants.iterator.next;
               if ((targetSet contains c) &&
                   (intervalSet getTermInterval c).containsInt(-negeq.constant));
               opt1 = (negeq > 0);
               opt2 = (negeq < 0))
          yield
            (List(opt1.negate, opt2.negate), "Negeq split on: " + negeq,
             null,
             List(Plugin.SplitDisequality(negeq, List(), List())))
  
        /**
         * Utilizes any gaps in an interval (i.e. x = [lb, -a] U [a, ub]) 
         *  and branches into two (i.e. x <= -a V x >= a)
         *
         */
        def gapSplit(intervalSet : IntervalSet,
                     targetSet : Set[ConstantTerm])
                    : Iterator[(Seq[ArithConj], String, BitSet,
                                Seq[Plugin.Action])] = {
          val gaps = intervalSet.getGaps
          (for ((term, interval, label) <- gaps.iterator;
                if (targetSet contains term))
          yield {
            val opt1 = (term < interval.gap.get._1)
            val opt2 = (term > interval.gap.get._2)
            (List(opt1.negate, opt2.negate),
             "Gap split on " + term + " using " + interval,
             label, null)
          })
        }

        ////////////////////////////////////////////////////////////////////////  

        addFacts(goal.facts.arithConj)

        var contPropLoop = true
        var lastAlternative : Seq[Plugin.Action] = null
        while (contPropLoop) {
          contPropLoop = false

          val intervalSet =
            new IntervalSet(preds,
                            ineqPolys.toVector, negeqPolys.toVector,
                            basicBounds.toVector)
  
          for ((_, _, l) <- intervalSet.getInconsistency) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            if (debug)
              println("ICP found inconsistency: " + label2Assumptions(l))
            //-END-ASSERTION-///////////////////////////////////////////////////
            return List(Plugin.CloseByAxiom(label2Assumptions(l),
                                            GroebnerMultiplication.this))
          }

          // Determine the constants considered for splitting
          val splitConstSet =
            if (MINIMAL_SPLITTING_SET)
              linearizers(predicates.toList, intervalSet)
            else
              (for (a <- predicates.iterator;
                    c <- a(0).constants.iterator ++ a(1).constants.iterator)
              yield c).toSet
          val splitConstSeq = new ArrayBuffer[ConstantTerm]
          splitConstSeq ++= order sort splitConstSet

          if (RANDOMISE_VARIABLE_ORDER)
            Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(splitConstSeq)

          val alternatives =
            negeqSplit(intervalSet,
                       goal.facts.arithConj.negativeEqs, splitConstSet) ++
            gapSplit(intervalSet, splitConstSet) ++
            (Param.NONLINEAR_SPLITTING(goal.settings) match {
              case Param.NonLinearSplitting.Sign |
                   Param.NonLinearSplitting.SignMinimal =>
                infinitySplit(intervalSet, splitConstSet) ++
                discreteSplit(intervalSet, splitConstSeq) ++
                binarySplit(intervalSet, splitConstSeq)
              case Param.NonLinearSplitting.Spherical =>
                throw new Exception("sphericalSplit not enabled!")
            })

          if (alternatives.hasNext) {
            val s@(options, desc, label, actions) = alternatives.next

            if (Param.PROOF_CONSTRUCTION(goal.settings)) {
              // just apply the split that we found
              val splitActions =
                if (actions == null)
                  List(Plugin.AxiomSplit(label2Assumptions(label),
                                         for (opt <- options)
                                           yield (conj(opt.negate), List()),
                                         GroebnerMultiplication.this))
                else
                  actions

              val intActions =
                filterActions(intervals2Actions(intervalSet, predicates, goal,
                                                label2Assumptions _), order)
              val res = intActions ++ splitActions

              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              printActions(desc, res)
              //-END-ASSERTION-/////////////////////////////////////////////////
              return res

            } else {

              val optionsBuf = new ArrayBuffer[ArithConj]
              optionsBuf ++= options

              if (RANDOMISE_CASES)
                Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(optionsBuf)

              lastAlternative =
                List(Plugin.AddFormula(intervals2Formula(intervalSet,
                                                         predicates, goal)),
                     Plugin.SplitGoal(for (opt <- optionsBuf)
                                      yield List(Plugin.AddFormula(conj(opt)))))


              //-BEGIN-ASSERTION-/////////////////////////////////////////////
              printActions(desc, lastAlternative)
              //-END-ASSERTION-///////////////////////////////////////////////
              return lastAlternative

/*
            TODO: do we still need the below code?

              val opt1act = Conjunction.conj(opt1, order)
              val opt2act = Conjunction.conj(opt2, order)

              // check whether we might be able to close one of the branches
              // immediately, in which case we can focus on the other branch

              if ((goal reduceWithFacts opt1).isFalse) {
                // note that we assume at this point that proof construction
                // is disabled, so the labels of formulas do not matter
                addFacts(opt1.negate)
//                println("one further iteration, adding " + opt1.negate)
                contPropLoop = true
              } else if ((goal reduceWithFacts opt2).isFalse) {
                // note that we assume at this point that proof construction
                // is disabled, so the labels of formulas do not matter
                addFacts(opt2.negate)
//                println("one further iteration, adding " + opt2.negate)
                contPropLoop = true
              } else {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                printActions(desc, lastAlternative)
                //-END-ASSERTION-///////////////////////////////////////////////
                return lastAlternative
              }
 */
            }

          } else if (lastAlternative != null) {

            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printActions("Splitting", lastAlternative)
            //-END-ASSERTION-///////////////////////////////////////////////////
            return lastAlternative

          } else {

            val intActions =
              filterActions(intervals2Actions(intervalSet, predicates,
                                              goal, label2Assumptions _), order)
            if (!intActions.isEmpty) {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              printActions("Implied intervals", intActions)
              //-END-ASSERTION-/////////////////////////////////////////////////
              return intActions
            }

          }
        }

        val retList = handleGoalAux(goal, true)
        if (retList.isEmpty)
          throw new Exception("ERROR: No splitting alternatives found")
  
        retList
      }
    }
  })

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def printNIAgoal(t : String, goal : Goal) = if (debug) {
    val muls = goal.facts.predConj.positiveLitsWithPred(_mul)
    val diseqs = goal.facts.arithConj.negativeEqs
    val ineqs = goal.facts.arithConj.inEqs

    println
    println(t)

    if (!muls.isEmpty) {
      println("+----------------------MUL------------------------------+")
      for (ex <- muls) {
        println("|\t" + ex)
      }
    }
    if (!diseqs.isEmpty) {
      println("+----------------------DISEQS---------------------------+")
      for (diseq <- diseqs) {
        println("|\t" + diseq + " != 0")
      }
    }
    if (!ineqs.isTrue) {
      println("+----------------------INEQS----------------------------+")
      for (ie <- ineqs) {
        println("|\t" + ie + " >= 0")
      }
    }
    println("+-------------------------------------------------------+")
  }

  private def printActions(t : String, actions : Seq[Plugin.Action]) : Unit =
    if (debug) {
      println(t + ":")
      for (a <- actions)
        println("\t" + a)
    }
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = "GroebnerMultiplication"
}
