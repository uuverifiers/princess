/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2025 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.basetypes.IdealInt
import ap.parser._
import ap.theories._
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.terfor.{TermOrder, ConstantTerm, Formula, ComputationLogger, Term}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.TerForConvenience._
import ap.util.IdealRange

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer, LinkedHashSet}

/**
 * Splitter handles the splitting when no new information can be deduced
 */
class Splitter(gbCache : GroebnerMultiplication.GBCache)
      extends TheoryProcedure {
  import GroebnerMultiplication._

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {

    // Compute a minimal set of variables that in enough to linearise all
    // multiplication atoms
    val MINIMAL_SPLITTING_SET = false
//      Param.NONLINEAR_SPLITTING(goal.settings) match {
//        case Param.NonLinearSplitting.SignMinimal => true
//        case _                                    => false
//      }

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

    ////////////////////////////////////////////////////////////////////////  

    addFacts(goal.facts.arithConj)

    var contPropLoop = true
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
                                        GroebnerMultiplication))
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
        infinitySplit(intervalSet, splitConstSet) ++
        discreteSplit(intervalSet, splitConstSeq) ++
        binarySplit(intervalSet, splitConstSeq)

      if (alternatives.hasNext) {
        val s@(options, desc, label, actions, canRandomise) =
          alternatives.next()

        if (Param.PROOF_CONSTRUCTION(goal.settings)) {
          // just apply the split that we found
          val splitActions =
            if (actions == null)
              List(Plugin.AxiomSplit(label2Assumptions(label),
                                      for (opt <- options)
                                        yield (conj(opt.negate), List()),
                                      GroebnerMultiplication))
            else
              actions

          // TODO: randomize

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

          if (canRandomise && RANDOMISE_CASES(goal))
            Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(optionsBuf)

          val alt =
            List(Plugin.AddFormula(intervals2Formula(intervalSet,
                                                      predicates, goal)),
                  Plugin.SplitGoal(for (opt <- optionsBuf)
                                  yield List(Plugin.AddFormula(conj(opt)))))


          //-BEGIN-ASSERTION-/////////////////////////////////////////////
          printActions(desc, alt)
          //-END-ASSERTION-///////////////////////////////////////////////
          return alt

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

/*
      } else if (lastAlternative != null) {

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////
        printActions("Splitting", lastAlternative)
        //-END-ASSERTION-///////////////////////////////////////////////////
        return lastAlternative
*/
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

    val retList = handleGoalAux(goal, goalState(goal), true, gbCache)
    if (retList.isEmpty)
      throw new Exception("ERROR: No splitting alternatives found")

    retList
  }

  /**
   * Here follow the different splitting strategies.
   */

  // General helper function, that find sets of ConstantTerms such that
  // all predicates are linearized
  // Since we have predicates of the form a(0)*a(1)=a(2), a simple (but incomplete?)

  def linearizers(predicates     : List[ap.terfor.preds.Atom],
                  intervalSet    : IntervalSet)
                 (implicit order : TermOrder) : Set[ConstantTerm] = {

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
  def infinitySplit(intervalSet    : IntervalSet,
                    targetSet      : Set[ConstantTerm])
                   (implicit order : TermOrder)
                    : Iterator[(Seq[ArithConj], String, BitSet,
                                Seq[Plugin.Action],
                                Boolean)] = {
    (intervalSet.getAllIntervals.iterator.collect {
      case (c, i, label) if ((targetSet contains c) &&
                              i.lower == IntervalNegInf &&
                              i.upper == IntervalPosInf) => {
        val opt1 = (c >= 0)
        val opt2 = (c < 0)
        (List(opt1.negate, opt2.negate),
          "[-Inf, +Inf] split: " + opt1 + ", " + opt2,
          BitSet(),
          splitTermAt(c, IdealInt.ZERO),
          true)
      }
    })
  }

  def splitTermAt(x              : ConstantTerm,
                  mid            : IdealInt,
                  swap           : Boolean = false)
                 (implicit order : TermOrder) : Seq[Plugin.Action] =
    if (swap)
      List(Plugin.CutSplit(x > mid, List(), List()))
    else
      List(Plugin.CutSplit(x <= mid, List(), List()))

  /**
   * Finds a possible split of x in [a, b] into the individual cases
   * x = a, x = a + 1, ..., x = b
   */ 
  def discreteSplit(intervalSet    : IntervalSet,
                    targetSet      : Seq[ConstantTerm])
                   (implicit order : TermOrder)
                  : Iterator[(Seq[ArithConj], String, BitSet,
                              Seq[Plugin.Action], Boolean)] = {
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
                                label1 | label2, null, true))
            }
            case _ =>
              Iterator.empty
          })
    yield res
  }

  /**
   * Splitting of intervals in the middle
   */ 
  def binarySplit(intervalSet    : IntervalSet,
                  targetSet      : Seq[ConstantTerm])
                 (implicit order : TermOrder)
                : Iterator[(Seq[ArithConj], String, BitSet,
                            Seq[Plugin.Action], Boolean)] = {
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
                                BitSet(), splitTermAt(x, mid), true))
            }
            case (Interval(IntervalVal(ll), IntervalPosInf, _), _)
                if ll.signum > 0 => {
              val mid = 2*ll
              val opt1 = ArithConj.conj(x <= mid, order)
              val opt2 = ArithConj.conj(x > mid, order)
              Iterator single ((List(opt1.negate, opt2.negate),
                                "Exp lowerbound split: " +
                                  opt1 + ", " + opt2,
                                BitSet(), splitTermAt(x, mid), false))
            }
            case (Interval(IntervalVal(ll), IntervalPosInf, _),
                  (label, _, _))
                if ll >= IdealInt.MINUS_ONE => {
              val opt1 = ArithConj.conj(x === ll, order)
              val opt2 = ArithConj.conj(x > ll, order)
              Iterator single ((List(opt1.negate, opt2.negate),
                                "LowerBound split: " + opt1 + ", " + opt2,
                                label, null, false))
            }
            case (Interval(IntervalNegInf, IntervalVal(ul), _), _)
                if ul.signum < 0 => {
              val mid = 2*ul
              val opt1 = ArithConj.conj(x > mid, order)
              val opt2 = ArithConj.conj(x <= mid, order)
              Iterator single ((List(opt1.negate, opt2.negate),
                                "Exp upperbound split: " +
                                  opt1 + ", " + opt2,
                                BitSet(), splitTermAt(x, mid, true),
                                false))
            }
            case (Interval(IntervalNegInf, IntervalVal(ul), _),
                  (_, label, _))
                if ul <= IdealInt.ONE => {
              val opt1 = ArithConj.conj(x === ul, order)
              val opt2 = ArithConj.conj(x < ul, order)
              Iterator single ((List(opt1.negate, opt2.negate),
                                "UpperBound split: " + opt1 + ", " + opt2,
                                label, null, false))
            }
            case (Interval(IntervalVal(_), IntervalPosInf, _), _) |
                (Interval(IntervalNegInf, IntervalVal(_), _), _) => {
              val opt1 = ArithConj.conj(x >= 0, order)
              val opt2 = ArithConj.conj(x < 0, order)
              Iterator single ((List(opt1.negate, opt2.negate),
                              "[-Inf, +Inf] split: " + opt1 + ", " + opt2,
                              BitSet(),
                              splitTermAt(x, IdealInt.ZERO),
                              true))
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
  def negeqSplit(intervalSet     : IntervalSet,
                  negeqs         : NegEquationConj,
                  targetSet      : Set[ConstantTerm])
                 (implicit order : TermOrder)
                : Iterator[(Seq[ArithConj], String, BitSet,
                            Seq[Plugin.Action], Boolean)] =
    for (negeq <- negeqs.iterator;
          if (negeq.constants.size == 1);
          c = negeq.constants.iterator.next();
          if ((targetSet contains c) &&
              (intervalSet getTermInterval c).containsInt(-negeq.constant));
          opt1 = (negeq > 0);
          opt2 = (negeq < 0))
    yield
      (List(opt1.negate, opt2.negate), "Negeq split on: " + negeq,
        null,
        List(Plugin.SplitDisequality(negeq, List(), List())),
        true)

  /**
   * Utilizes any gaps in an interval (i.e. x = [lb, -a] U [a, ub]) 
   *  and branches into two (i.e. x <= -a V x >= a)
   */
  def gapSplit(intervalSet     : IntervalSet,
                targetSet      : Set[ConstantTerm])
               (implicit order : TermOrder)
              : Iterator[(Seq[ArithConj], String, BitSet,
                          Seq[Plugin.Action], Boolean)] = {
    val gaps = intervalSet.getGaps
    (for ((term, interval, label) <- gaps.iterator;
          if (targetSet contains term))
    yield {
      val opt1 = (term < interval.gap.get._1)
      val opt2 = (term > interval.gap.get._2)
      (List(opt1.negate, opt2.negate),
        "Gap split on " + term + " using " + interval,
        label, null, true)
    })
  }
}
