/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.Signature
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Term, Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.inequalities.InEqConj
import ap.proof.goal.{Goal, TaskAggregator}
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.tree.NonRandomDataSource
import ap.parser.{IFunction, ITerm, IFormula, IAtom}
import ap.parameters.Param
import ap.util.{IdealRange, Debug}

import IdealInt.pow2MinusOne

object IntValueEnumTheory {

  private val AC = Debug.AC_VALUE_ENUMERATOR

}

/**
 * A theory for explicitly enumerating all values of integer
 * terms. The proof procedure that will take care of the splitting
 * will be given the priority specified by
 * <code>splitterCost</code>. The splitting of the value range of
 * terms will initially be binary; once the range of possible values
 * of a term has been narrowed down to at most
 * <code>completeSplitBound</code> values, in a single step the range
 * will be split into all individual values. In order to initiate
 * splitting, literals <code>IntValueEnumTheory.enumPred(t)</code>
 * have to be added to a proof goal.
 */
class IntValueEnumTheory(name               : String,
                         splitterCost       : Int = 0,
                         completeSplitBound : Int = 20,
                         randomiseValues    : Boolean = true) extends Theory {

  import IntValueEnumTheory._

  /**
   * Generate an assertion that will cause all values of the given
   * term to be enumerated explicitly. The enumeration will be
   * fair, i.e., every possible value of the term will be considered
   * eventually.
   */
  def enumIntValuesOf(t : Term, order : TermOrder) : Formula =
    Atom(enumPred, List(LinearCombination(t, order)), order)

  /**
   * Generate an assertion that will cause all values of the given
   * term to be enumerated explicitly. The enumeration will be
   * fair, i.e., every possible value of the term will be considered
   * eventually.
   */
  def enumIntValuesOf(t : ITerm) : IFormula =
    IAtom(enumPred, Seq(t))

  val enumPred                 = new Predicate(name + "_enum", 1)

  // magnitudeBoundPred(n, t) expresses that |t| >= 2^n - 1
  val magnitudeBoundPred       = new Predicate(name + "_mag_bigger_than", 2)

  val functions                = List()
  val predicates               = List(enumPred, magnitudeBoundPred)
  val axioms                   = Conjunction.TRUE
  val totalityAxioms           = Conjunction.TRUE
  val functionPredicateMapping = List()

  val predicateMatchConfig     : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction]                 = Set()
  val functionalPredicates     : Set[Predicate]                 = Set()

  private val initialBoundLog = {
    var b = 0
    while (completeSplitBound >= (1 << (b + 2)))
      b = b + 1
    b
  }

  private object Splitter extends TheoryProcedure {
    def boundLitsFor(goal : Goal,
                     enumTerm : LinearCombination) : Seq[Atom] = {
      val facts     = goal.facts
      val boundLits = facts.predConj.positiveLitsWithPred(magnitudeBoundPred)

      boundLits filter { a => a(1) == enumTerm }
    }

    def elimBoundPreds(goal : Goal,
                       enumTerm : LinearCombination) : Seq[Plugin.Action] = {
      implicit val order = goal.order
      import TerForConvenience._

      val facts     = goal.facts
      val boundLits = facts.predConj.positiveLitsWithPred(magnitudeBoundPred)

      for (lit <- boundLitsFor(goal, enumTerm);
           bound = pow2MinusOne(lit(0).constant.intValueSafe);
           act <- List(Plugin.RemoveFacts(conj(lit)),
                       Plugin.AddAxiom(
                         List(lit),
                         !((enumTerm > -bound) & (enumTerm < bound)),
                         IntValueEnumTheory.this)))
      yield act
    }

    def splitInterval(goal     : Goal,
                      enumTerm : LinearCombination,
                      lb       : IdealInt,
                      lbAss    : Seq[LinearCombination],
                      ub       : IdealInt,
                      ubAss    : Seq[LinearCombination]) : Seq[Plugin.Action] ={
      implicit val order = goal.order
      import TerForConvenience._

      val rand =
        if (randomiseValues)
          Param.RANDOM_DATA_SOURCE(goal.settings)
        else
          NonRandomDataSource

      if (ub - lb > IdealInt(completeSplitBound)) {

        val mid = (ub + lb) / 2
        if (rand.nextBoolean)
          List(Plugin.CutSplit(enumTerm > mid, List(), List()))
        else
          List(Plugin.CutSplit(enumTerm <= mid, List(), List()))

      } else {

        List(Plugin.AxiomSplit(
               for (lc <- lbAss ++ ubAss) yield InEqConj(lc, order),
               rand.shuffleSeq(
                 for (k <- IdealRange(lb, ub + 1)) yield {
                   (conj(enumTerm === k), List())
                 }),
               IntValueEnumTheory.this
             ))

      }
    }

    def magnitudeSplit(goal                : Goal,
                       enumTerm            : LinearCombination,
                       boundLog            : Int,
                       secondBranchActions : Seq[Plugin.Action])
                                           : Seq[Plugin.Action] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, boundLog >= 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val bound = pow2MinusOne(boundLog)

      implicit val order = goal.order
      import TerForConvenience._

      List(Plugin.AxiomSplit(
             List(),
             List(((enumTerm > -bound) & (enumTerm < bound),
                   List()),
                  (magnitudeBoundPred(List(l(boundLog), enumTerm)),
                   secondBranchActions)),
             IntValueEnumTheory.this))
    }


    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val order = goal.order
      import TerForConvenience._

      val facts     = goal.facts
      val enumLits  = facts.predConj.positiveLitsWithPred(enumPred)

      if (enumLits.isEmpty) {
        List()
      } else {
        val rand      = Param.RANDOM_DATA_SOURCE(goal.settings)
        val reducer   = goal.reduceWithFacts
        val enumLit   = enumLits(rand nextInt enumLits.size)
        val enumTerm  = enumLit(0)

        val lbOpt     = reducer.lowerBoundWithAssumptions(enumTerm)
        val ubOpt     = reducer.upperBoundWithAssumptions(enumTerm)

        val actions =
          (lbOpt, ubOpt) match {
            case (Some((lb, lbAss)), Some((ub, ubAss))) => {
              elimBoundPreds(goal, enumTerm) elseDo
              splitInterval(goal, enumTerm, lb, lbAss, ub, ubAss)
            }
            case _ => {
              boundLitsFor(goal, enumTerm) match {
                case Seq() => {
                  magnitudeSplit(goal, enumTerm, initialBoundLog, List())
                }
                case Seq(boundLit, _*) => {
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(AC, boundLit(0).isConstant)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  val boundLog = boundLit(0).constant.intValueSafe
                  magnitudeSplit(goal, enumTerm, boundLog + 1,
                                 List(Plugin.RemoveFacts(boundLit)))
                }
              }
            }
          }

        List(scheduleSplitter) ++ actions
      }
    }
  }

  private val scheduleSplitter = Plugin.ScheduleTask(Splitter, splitterCost)

  val plugin = Some(
    new Plugin {
      override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
        val facts    = goal.facts
        val enumLits = facts.predConj.positiveLitsWithPred(enumPred)

        if (enumLits.isEmpty) {
          List()
        } else {
          implicit val order = goal.order
          import TerForConvenience._

          val splitterActions =
            if (goal.tasks.taskSummaryFor(
                  TaskAggregator.ScheduledTheoryProcedureCounter).contains(
                    Splitter)) {
              List()
            } else {
              List(scheduleSplitter)
            }

          val enumActions =
            for (lit <- enumLits; if lit.last.isConstant)
            yield Plugin.RemoveFacts(conj(lit))

          val boundActions =
            for (lit <- facts.predConj.positiveLitsWithPred(magnitudeBoundPred);
                 if lit.last.isConstant;
                 bound = pow2MinusOne(lit.head.constant.intValueSafe);
                 constraint = lit.last <= -bound | lit.last >= bound;
                 act <- List(Plugin.RemoveFacts(conj(lit))) ++ (
                   if (constraint.isTrue)
                     List()
                   else
                     List(Plugin.AddAxiom(List(lit), constraint,
                                          IntValueEnumTheory.this))))
            yield act

          splitterActions ++ enumActions ++ boundActions
        }
      }
    })

  override def isSoundForSat(
    theories : Seq[Theory],
    config : Theory.SatSoundnessConfig.Value) : Boolean = true

  override def toString = name

  TheoryRegistry register this

}
