/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.theoryPlugins;

import ap.proof.goal.{Goal, Task, EagerTask, PrioritisedTask}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

import scala.collection.mutable.{Stack, ArrayBuffer}

object Plugin {
  protected[theoryPlugins] val AC = Debug.AC_PLUGIN

  abstract sealed class Action
  case class AddFormula  (formula : Conjunction)    extends Action
  case class RemoveFacts (facts : Conjunction)      extends Action
  case class SplitGoal   (cases : Seq[Seq[Action]]) extends Action
  case class ScheduleTask(proc : TheoryProcedure,
                          priority : Int)           extends Action

  object GoalState extends Enumeration {
    val Intermediate, Final = Value
  }
}

/**
 * General interface for a theory-specific procedure that
 * can be applied by a prover to reason about interpreted symbols.
 */
trait TheoryProcedure {

  import Plugin.GoalState

  /**
   * Apply this procedure to the given goal.
   */
  def handleGoal(goal : Goal) : Seq[Plugin.Action]

  /**
   * Try to determine in which state a given goal is.
   */
  def goalState(goal : Goal) : GoalState.Value =
    if (goal.tasks.finalEagerTask) GoalState.Final else GoalState.Intermediate

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Interface for theory plugins that can be added to the
 * <code>EagerTaskManager</code>. At the moment, such plugins
 * can mainly observe which formulae are asserted on a branch,
 * and then generate/instantiate further axioms to add
 * theory knowledge.
 *
 * Plugin objects have to be immutable.
 */
trait Plugin extends TheoryProcedure {

  /**
   * Given the current goal, possible generate (local and global) axioms.
   */
  def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)]

  /**
   * Apply this plugin to the given goal. The default procedure
   * is to call <code>generateAxioms</code>, and possibly add further
   * facts or axioms to the goal.
   */
  def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    generateAxioms(goal) match {
      case Some((localAxioms, globalAxioms)) => {
        val allAxioms = Conjunction.conj(List(localAxioms, globalAxioms),
                                         goal.order).negate
        List(Plugin.AddFormula(allAxioms))
      }
      case None =>
        List()
    }

  /**
   * Check whether the formulas in the given goal are satisfiable,
   * and if yes generate a model. The returned
   * formula is meant to replace the goal facts in this case.
   */
  def generateModel(goal : Goal) : Option[Conjunction] = None

}

////////////////////////////////////////////////////////////////////////////////

object PluginSequence {
  def apply(plugins : Seq[Plugin]) : Option[Plugin] = plugins match {
    case Seq()       => None
    case Seq(plugin) => Some(plugin)
    case plugins     => {
      val flatPlugins =
        for (p <- plugins;
             q <- p match {
               case p : PluginSequence => p.plugins
               case p => List(p)
             })
        yield q
      Some(new PluginSequence(flatPlugins))
    }
  }
}

/**
 * Execution of a sequence of plugins.
 */
class PluginSequence private (val plugins : Seq[Plugin]) extends Plugin {

  // not used
  def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
    throw new UnsupportedOperationException

  override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    val it = plugins.iterator
    var res : Seq[Plugin.Action] = List()
    while (res.isEmpty && it.hasNext)
      res = it.next handleGoal goal
    res
  }

  /**
   * Check whether the formulas in the given goal are satisfiable,
   * and if yes generate a model. The returned
   * formula is meant to replace the goal facts in this case.
   */
  override def generateModel(goal : Goal) : Option[Conjunction] = {
    val it = plugins.iterator
    var res : Option[Conjunction] = None
    while (!res.isDefined && it.hasNext)
      res = it.next generateModel goal
    res
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Task integrating a <code>Plugin</code> (or <code>TheoryProcedure</code>)
 * into a prover
 */
abstract class PluginTask(plugin : TheoryProcedure) extends Task {
  import Plugin._

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val actions = plugin handleGoal goal

    if (actions.isEmpty) {
      ptf.updateGoal(goal)
    } else actions.last match {

      case _ : SplitGoal => {
        val actionStack    = new Stack[Seq[Action]]
        val resultingTrees = new ArrayBuffer[ProofTree]

        actionStack push actions

        while (!actionStack.isEmpty) {
          val actions = actionStack.pop
          if (actions.isEmpty) {
            resultingTrees += ptf.updateGoal(goal)
          } else actions.last match {
            case SplitGoal(subActions) => {
              val otherActions = actions.init
              for (b <- subActions.reverseIterator)
                actionStack push (otherActions ++ b)
            }
            case _ => {
              resultingTrees += applyActions(actions, goal, ptf)
            }
          }
        }

        ptf.and(resultingTrees, goal.vocabulary)
      }

      case _ =>
        applyActions(actions, goal, ptf)
    }
  }

  private def applyActions(actions : Seq[Action],
                           goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(Plugin.AC, !(actions exists (_.isInstanceOf[SplitGoal])))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val factsToRemove =
      Conjunction.conj(for (RemoveFacts(f) <- actions.iterator) yield f,
                       goal.order)
    val factsToAdd =
      goal.reduceWithFacts(
        Conjunction.disj(for (AddFormula(f) <- actions.iterator) yield f,
                         goal.order))

    val tasksToSchedule =
      (for (ScheduleTask(proc, priority) <- actions.iterator)
       yield new PrioritisedPluginTask(proc, priority, goal.age)).toList
    val formulaTasks =
      (goal formulaTasks factsToAdd)

    val newFacts =
      if (factsToRemove.isTrue)
        goal.facts
      else
        goal.facts -- factsToRemove

    val allFormulaTasks =
      if (formulaTasks.isEmpty &&
          (actions exists {
             case AddFormula(_) | RemoveFacts(_) => true
             case _ => false
           }) &&
          !newFacts.isTrue) {
        // we have to make sure that the plugin is called a a further time,
        // otherwise we get very confusing semantics
        // just add a formula that we already know about
        goal formulaTasks !newFacts.iterator.next
      } else {
        formulaTasks
      }

    ptf.updateGoal(newFacts,
                   tasksToSchedule ++ allFormulaTasks,
                   goal)
  }
}

////////////////////////////////////////////////////////////////////////////////

class EagerPluginTask(plugin : TheoryProcedure)
      extends PluginTask(plugin) with EagerTask {
  override def toString = "EagerPluginTask(" + plugin + ")"
}

////////////////////////////////////////////////////////////////////////////////

class PrioritisedPluginTask(plugin : TheoryProcedure,
                            basePriority : Int,
                            age : Int)
      extends PluginTask(plugin) with PrioritisedTask {

  val priority : Int = basePriority + age
 
  /**
   * Update the task with possibly new information from the goal.
   * Currently, this does not modify the theory procedure.
   */
  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[PrioritisedTask] =
    List(this)

  override def toString = "PrioritisedPluginTask(" + plugin + ")"
}
