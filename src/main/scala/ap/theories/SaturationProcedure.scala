/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024-2026 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.parser.IFunction
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.proof.theoryPlugins.TheoryProcedure
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs}

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}

object AbstractSaturationProcedure {

  protected[theories] val AC = Debug.AC_THEORY

}

abstract class AbstractSaturationProcedure(val name : String) extends Theory {

  /**
   * Type representing the cases in which the saturation procedure applies.
   * Those could be formulas or terms occurring in a goal, etc.
   */
  type ApplicationPoint

  /**
   * Determine all points at which this saturation procedure could be applied
   * in a goal.
   */
  def extractApplicationPoints(goal : Goal) : Iterator[ApplicationPoint]

  /**
   * The priority of performing the given saturation. Lower numbers
   * represent higher priority.
   */
  def applicationPriority(goal : Goal, p : ApplicationPoint) : Int

  /**
   * Actions to be performed for one particular application point. The method
   * should check whether the application
   * point still exists in the goal; in case the application point has already
   * disappeared from the goal at the point of calling this method, the method
   * should return an empty sequence.
   */
  def handleApplicationPoint(goal : Goal,
                             p : ApplicationPoint) : Seq[Plugin.Action]

}

/**
 * Class to simplify the implementation of saturation procedures as part of
 * theory plugins. A saturation procedure is a procedure waiting for patterns
 * to occur in a proof goal (e.g., formulas of a certain shape), and can apply
 * proof rules for every such occurrence. Saturation will be implemented by
 * adding tasks to the task queue of every goal, so that the prover can globally
 * schedule the different rules to be applied.
 * 
 * This procedure does not take into account that applications points might get
 * rewritten during the proof process; e.g., a variable <code>x</code> could
 * turn into <code>y</code> when the equation <code>x = y</code> appears. In such
 * cases, the saturation rule could get applied repeatedly for the same point.
 */
abstract class SaturationProcedure(_name : String)
         extends AbstractSaturationProcedure(_name) {
  import AbstractSaturationProcedure._

  /**
   * Scheduled tasks of the saturation procedure. Each of those tasks
   * takes care of one application point.
   */
  class PointHandler(val point : ApplicationPoint) extends TheoryProcedure {
    val saturationProcedure : SaturationProcedure = SaturationProcedure.this
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      handleApplicationPoint(goal, point)
    override def toString = name + "_handler"
  }

  override def plugin = Some(
    new Plugin {
      private val theory = SaturationProcedure.this

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
        goalState(goal) match {
          case Plugin.GoalState.Final | Plugin.GoalState.Intermediate => {
            import TerForConvenience._
            import Plugin.{AddAxiom, ScheduleTask}

            implicit val order : TermOrder = goal.order
            val predFacts = goal.facts.predConj

            val idsInGoal =
              (for (a <- predFacts.positiveLitsWithPred(pointPred)) yield {
                 val t = a(0)
                 //-BEGIN-ASSERTION-///////////////////////////////////////////
                 Debug.assertInt(AC, t.isConstant)
                 //-END-ASSERTION-/////////////////////////////////////////////
                 t.constant.intValueSafe
               }).toSet

            (for (p       <- extractApplicationPoints(goal);
                  id      = point2id(p);
                  if !(idsInGoal contains id);
                  prio    = applicationPriority(goal, p);
                  act1    = AddAxiom(List(), pointPred(List(l(id))), theory);
                  act2    = ScheduleTask(new PointHandler (p), prio);
                  act     <- Iterator(act1, act2))
             yield act).toIndexedSeq
          }
          case _ =>
            List()
        }

      override def toString = name + "_scanner"
    }
  )

  private val point2idMap      = new MHashMap[ApplicationPoint, Int]
  private val id2pointMap      = new MHashMap[Int, ApplicationPoint]

  def point2id(p : ApplicationPoint) : Int =
    synchronized {
      point2idMap.getOrElseUpdate(p, {
        val id = point2idMap.size
        id2pointMap.put(id, p)
        id
      })
    }

  def id2point(id : Int) : ApplicationPoint =
    synchronized { id2pointMap(id) }

  /**
   * Predicate to record, in a proof goal, that a handler has been spawned
   * for a certain application point. This is done by assigning a unique
   * id to every application point; the argument of this predicate is the id.
   */
  val pointPred                = new Predicate(name + "_spawned", 1)

  val functions                = List()
  val predicates               = List(pointPred)
  val axioms                   = Conjunction.TRUE
  val totalityAxioms           = Conjunction.TRUE
  val functionPredicateMapping = List()

  val predicateMatchConfig     : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction]                 = Set()
  val functionalPredicates     : Set[Predicate]                 = Set()

  override def isSoundForSat(
    theories : Seq[Theory],
    config : Theory.SatSoundnessConfig.Value) : Boolean = true

  override def toString = name

  TheoryRegistry register this

}

/**
 * Class to simplify the implementation of saturation procedures as part of
 * theory plugins. A saturation procedure is a procedure waiting for patterns
 * to occur in a proof goal (e.g., formulas of a certain shape), and can apply
 * proof rules for every such occurrence. Saturation will be implemented by
 * adding tasks to the task queue of every goal, so that the prover can globally
 * schedule the different rules to be applied.
 * 
 * This version of a saturation procedure only supports rules whose application
 * points can be specified using a fixed-arity vector of terms, for instance
 * the arguments of certain atoms occurring in a proof goal. The procedure
 * takes simplification of terms occurring in the proof goal into account. It is
 * defined in such a way that application points that occur repeatedly can also
 * lead to repeated application of the rule. Application points are handled by
 * a single task (with priority <code>basePriority</code>) added to the task
 * queue, which will always pick the application point with the highest
 * priority and apply the defined handler to it. The flag
 * <code>priorityUpdates</code> enables continuous updates of the priority of
 * application points.
 */
abstract class TermBasedSaturationProcedure(_name           : String,
                                            arity           : Int,
                                            basePriority    : Int,
                                            priorityUpdates : Boolean = false)
         extends AbstractSaturationProcedure(_name) {
  import AbstractSaturationProcedure._

  type ApplicationPoint = Seq[LinearCombination]

  /**
   * Scheduled tasks of the saturation procedure. Each of those tasks
   * takes care of one application point.
   */
  object PointHandler extends TheoryProcedure {
    val saturationProcedure : TermBasedSaturationProcedure =
      TermBasedSaturationProcedure.this

    def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      import TerForConvenience._
      implicit val order : TermOrder = goal.order
      val predConj = goal.facts.predConj
      val po = order.reversePredOrdering

      // find the application point with the highest priority for which
      // rules are applicable
      val upperBound = Seqs.risingEdge(predConj.positiveLits,
                                       (a:Atom) => po.gt(a.pred, pointPred))

      var nextInd = upperBound - 1
      var actions : Seq[Plugin.Action] = List()
      val atomsToRemove = new ArrayBuffer[Atom]

      while (actions.isEmpty && nextInd >= 0 &&
             predConj.positiveLits(nextInd).pred == pointPred) {
        val atom = predConj.positiveLits(nextInd)
        val point = atom.toSeq.drop(2)
        atomsToRemove += atom
        actions = handleApplicationPoint(goal, point)
        nextInd = nextInd - 1
      }

      val scheduleActions =
        if (nextInd >= 0 && predConj.positiveLits(nextInd).pred == pointPred)
          // schedule another handler to take care of the next application
          // points
          List(scheduleHandlerAction)
        else
          List()

      val removalActions =
        if (atomsToRemove.isEmpty)
          List()
        else
          List(Plugin.RemoveFacts(conj(atomsToRemove)))

      removalActions ++ scheduleActions ++ actions
    }

    override def toString = name + "_handler"
  }

  private val scheduleHandlerAction =
    Plugin.ScheduleTask(PointHandler, basePriority)

  private def handleApplicationPoints(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    import Plugin.AddAxiom

    implicit val order : TermOrder = goal.order
    val predFacts                  = goal.facts.predConj
    val age                        = goal.age

    val pointAtoms                 = predFacts.positiveLitsWithPred(pointPred)
    val pointsInGoal : Set[ApplicationPoint] = pointAtoms.map(_.toSeq.drop(2)).toSet

    val newPoints =
      (for (p <- extractApplicationPoints(goal);
            if {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(AC, p.size == arity)
              //-END-ASSERTION-/////////////////////////////////////////////////
              !(pointsInGoal contains p)
            };
            prio = applicationPriority(goal, p);
            args = List(l(prio + age), l(age)) ++ p;
            act  = AddAxiom(List(), pointPred(args), this))
      yield act).toIndexedSeq

    val newTasks =
      if (pointsInGoal.isEmpty && !newPoints.isEmpty)
        List(scheduleHandlerAction)
      else
        List()

    val updates =
      if (priorityUpdates && !pointAtoms.isEmpty)
        updatePriorities(goal, pointAtoms)
      else
        List()

    newPoints ++ newTasks ++ updates
  }

  private def updatePriorities(goal       : Goal,
                               pointAtoms : Seq[Atom]) : Seq[Plugin.Action] = {
    import TerForConvenience._
    import Plugin.{AddAxiom, RemoveFacts}

    implicit val order : TermOrder = goal.order
    val predFacts                  = goal.facts.predConj

    val toRemove                   = new ArrayBuffer[Atom]
    val actions                    = new ArrayBuffer[Plugin.Action]

    for (a <- pointAtoms) {
      val LinearCombination.Constant(oldPrio) = a(0)
      val LinearCombination.Constant(age)     = a(1)
      val newPrio = age + applicationPriority(goal, a.toSeq.drop(2))
      if (newPrio != oldPrio) {
        toRemove += a
        actions +=
          AddAxiom(List(), pointPred(List(l(newPrio)) ++ a.toSeq.drop(1)), this)
      }
    }

    if (!actions.isEmpty)
      actions += RemoveFacts(conj(toRemove))

    actions.toSeq
  }

  override def plugin = Some(
    new Plugin {
      override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
        goalState(goal) match {
          case Plugin.GoalState.Final | Plugin.GoalState.Intermediate => 
            handleApplicationPoints(goal)
          case _ =>
            List()
        }

      override def toString = name + "_scanner"
    }
  )

  /**
   * Predicate to record, in a proof goal, that a vector of terms was identified
   * as an application point. The predicate also stores the priority of the
   * application point (first argument, lower number means higher priority) and
   * the age of the application point (second argument).
   */
  val pointPred                = new Predicate(name + "_app", arity + 2)

  val functions                = List()
  val predicates               = List(pointPred)
  val axioms                   = Conjunction.TRUE
  val totalityAxioms           = Conjunction.TRUE
  val functionPredicateMapping = List()

  val predicateMatchConfig     : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction]                 = Set()
  val functionalPredicates     : Set[Predicate]                 = Set()

  override def isSoundForSat(
    theories : Seq[Theory],
    config : Theory.SatSoundnessConfig.Value) : Boolean = true

  override def toString = name

  TheoryRegistry register this

}