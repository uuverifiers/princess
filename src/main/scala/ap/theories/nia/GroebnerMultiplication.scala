/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2026 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.basetypes.IdealInt
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
import ap.util.{Timeout, Seqs, Debug, LRUCache, IdealRange}

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer, LinkedHashSet}

/**
 * Implementation of a theory of non-linear integer arithmetic.
 * Currently the theory does Groebner basis calculation followed
 * by interval propagation.
 */
object GroebnerMultiplication extends MulTheory {
  import Buchberger._

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
  //val RANDOMISE_CASES = true
  def RANDOMISE_CASES(goal : Goal) =
    Param.NONLINEAR_SPLITTING_ORDER(goal.settings) ==
      Param.NonLinearSplittingOrder.VarsCases

  // Use the IntValueEnumerator theory instead of the native splitter
  // val VALUE_ENUMERATOR = false
  def VALUE_ENUMERATOR(goal : Goal) =
    Param.NONLINEAR_SPLITTING(goal.settings) ==
      Param.NonLinearSplitting.Spherical

  // Maximum number of refinements accepted per variable during ICP before
  // considering the variable as "unstable"
  val PROPAGATION_UPDATE_LIMIT = 5

  // Max size of intervals that are considered "small" during ICP
  val SMALL_INTERVAL_BOUND = 100

  // Priority used for the task splitting value ranges
  val SPLITTER_BASE_PRIORITY = 0

  protected[nia] val AC = Debug.AC_NIA

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

  val valueEnumerator : IntValueEnumTheory =
      new IntValueEnumTheory("GroebnerMultiplicationValueEnumerator",
                             completeSplitBound = DISCRETE_SPLITTING_LIMIT,
                             splitterCost = SPLITTER_BASE_PRIORITY,
                             randomiseValues = true)

  override val dependencies = List(valueEnumerator)

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

  protected[nia] type GBCache =
    LRUCache[(Seq[Atom], TermOrder), (Basis, Seq[Atom], MonomialOrdering)]

  def plugin = Some(new Plugin {

    private val gbCache = new GBCache (5)

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
      
        handleGoalAux(goal, goalState(goal), false, gbCache)

      }
    }
  })

  /////////////////////////////////////////////////////////////////////////////

  protected[nia] def handleGoalAux(goal                : Goal,
                                    gState             : Plugin.GoalState.Value,
                                    calledFromSplitter : Boolean,
                                    gbCache            : GBCache)
                                                       : Seq[Plugin.Action] = {
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

    // Did we find any linear formulas that can be propagated back?
    val linearEq = simplifiedGB.toArray
    if (!linearEq.isEmpty) {
      if (linearEq forall (_.isLinear)) {

        val actions =
          (for (p <- linearEq.iterator;
                c = polynomialToAtom(p))
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
            if (remainingPoly.isLinear) {
              val factorisation =
                disjFor(List(polynomialToAtom(remainingPoly)) ++
                        (for (v <- factor.variables) yield (v === 0)))
              actions = Plugin.AddAxiom(assumptions,
                                        factorisation,
                                        GroebnerMultiplication.this) :: actions
            }
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

    if (VALUE_ENUMERATOR(goal)) {
      val linearizer = simpleLinearizers(goal)
      val enumAtoms =
        goal.reduceWithFacts(
          conj(linearizer.map(valueEnumerator.enumIntValuesOf(_, order))))
      if (enumAtoms.isTrue)
        List()
      else
        List(Plugin.AddAxiom(List(), enumAtoms, this))
    } else if (calledFromSplitter) {
      List()
    } else {
      val splitter = new Splitter(gbCache)

      gState match {
        case Plugin.GoalState.Eager =>
          List()
        case Plugin.GoalState.Intermediate => {
          // Schedule a task to take care of the splitting
          val scheduleAction =
            Plugin.ScheduleTask(splitter, SPLITTER_BASE_PRIORITY)
          removeFactsActions ::: List(scheduleAction)
        }
        case Plugin.GoalState.Final =>
          // Split directly!
          removeFactsActions ::: (splitter handleGoal goal).toList
      }
    }

  }

  /////////////////////////////////////////////////////////////////////////////

  /**
   * Generate linear approximations of quadratic terms using
   * cross-multiplication. This version only considers inequalities
   * with exactly one constant symbol.
   */
  private def crossMult(intervalSet       : IntervalSet,
                        predicates        : IndexedSeq[Atom],
                        goal              : Goal,
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

  /////////////////////////////////////////////////////////////////////////////

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

  /////////////////////////////////////////////////////////////////////////////

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

  /////////////////////////////////////////////////////////////////////////////

  protected[nia] def intervals2Formula(intervalSet : IntervalSet,
                                       predicates  : IndexedSeq[Atom],
                                       goal        : Goal)
                                                   : Conjunction = {
    implicit val _ = goal.order

    (goal reduceWithFacts conj(
        for (Plugin.AddAxiom(_, f, _) <-
              intervals2Actions(intervalSet, predicates,
                                goal, l => List()).iterator)
        yield f)).negate
  }

  protected[nia] def intervals2Actions(intervalSet       : IntervalSet,
                                       predicates        : IndexedSeq[Atom],
                                       goal              : Goal,
                                       label2Assumptions : BitSet => Seq[Formula])
                                                         : Seq[Plugin.Action] = {
    implicit val order = goal.order

    val intervalAtoms = new ArrayBuffer[(ArithConj, BitSet)]

    for ((ct, i, (l1, l2, _)) <- intervalSet.getStableUpdatedIntervals) {

      if (i.lower == i.upper) {
        i.lower match {
          case IntervalVal(v) => intervalAtoms += ((ct === v, l1 | l2))
          case _ => // nothing
        }
      } else {
        // Generate inequalities according to intervals
        i.lower match {
          case IntervalNegInf =>
          case IntervalPosInf => {
            intervalAtoms += ((ct > 0, l1))
            intervalAtoms += ((ct < 0, l1))
          }
          case IntervalVal(v) =>
            intervalAtoms += ((ct >= v, l1))
        }

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

    (for ((f, label) <- intervalAtoms.iterator;
          if !(goal reduceWithFacts f).isTrue)
      yield (Plugin.AddAxiom(label2Assumptions(label), conj(f),
                            GroebnerMultiplication.this))).toList
  }

  protected[nia] def filterActions(actions : Seq[Plugin.Action],
                                   order   : TermOrder)
                                           : Seq[Plugin.Action] =
    actions filter (Plugin.isRelevantAxiomAction(_, order))

  /**
   * Find a set of constants that are sufficient to make all product
   * constraints linear: assigning concrete values to the constants will
   * make products become linear.
   */
  def simpleLinearizers(goal : Goal) : Set[ConstantTerm] = {
    implicit val order =
      goal.order
    val predicates =
      goal.facts.predConj.positiveLitsWithPred(_mul)
    val predSet =
      for (p <- predicates) yield (p(0).constants, p(1).constants)
    val relevantConsts =
      (for ((s, t) <- predSet.iterator; c <- s.iterator ++ t.iterator)
        yield c).toSet

    val allConsts = order.sort(relevantConsts)
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

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  protected[nia] def printNIAgoal(t : String, goal : Goal) = if (debug) {
    val muls = goal.facts.predConj.positiveLitsWithPred(_mul)
    val diseqs = goal.facts.arithConj.negativeEqs
    val ineqs = goal.facts.arithConj.inEqs

    println()
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

  protected[nia] def printActions(t : String, actions : Seq[Plugin.Action]) : Unit =
    if (debug) {
      println(t + ":")
      for (a <- actions)
        println("\t" + a)
    }
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = "GroebnerMultiplication"
}
