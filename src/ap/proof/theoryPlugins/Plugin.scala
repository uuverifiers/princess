/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.theoryPlugins;

import ap.proof.goal.{Goal, EagerTask}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug


object Plugin {
  abstract sealed class Action
  case class AddFormula(formula : Conjunction) extends Action
  case class RemoveFacts(facts : Conjunction)  extends Action
}

/**
 * Interface for theory plugins that can be added to the
 * <code>EagerTaskManager</code>. At the moment, such plugins
 * can mainly observe which formulae are asserted on a branch,
 * and then generate/instantiate further axioms to add
 * theory knowledge.
 *
 * Plugin objects have to be immutable.
 */
trait Plugin {

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

}

////////////////////////////////////////////////////////////////////////////////

class AxiomGenTask(plugin : Plugin) extends EagerTask {
  import Plugin._

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val actions = plugin handleGoal goal

    val factsToRemove =
      Conjunction.conj(for (RemoveFacts(f) <- actions.iterator) yield f,
                       goal.order)
    val factsToAdd =
      goal.reduceWithFacts(
        Conjunction.disj(for (AddFormula(f) <- actions.iterator) yield f,
                         goal.order))

    if (factsToRemove.isTrue) {
      if (factsToAdd.isFalse)
        ptf.updateGoal(goal)
      else
        ptf.updateGoal(goal formulaTasks factsToAdd, goal)
    } else {
      val remainingFacts = goal.facts -- factsToRemove
      if (factsToAdd.isFalse)
        ptf.updateGoal(remainingFacts, goal)
      else
        ptf.updateGoal(remainingFacts,
                       goal formulaTasks factsToAdd,
                       goal)
    }
  }

  override def toString = "AxiomGenTask(" + plugin + ")"
}
