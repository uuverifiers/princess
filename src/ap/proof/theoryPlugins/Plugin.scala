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

}

////////////////////////////////////////////////////////////////////////////////

class AxiomGenTask(plugin : Plugin) extends EagerTask {
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    (plugin generateAxioms goal) match {
      case Some((localAxioms, globalAxioms)) => {
        val allAxioms = Conjunction.conj(List(localAxioms, globalAxioms),
                                         goal.order).negate
        ptf.updateGoal(goal formulaTasks (goal reduceWithFacts allAxioms), goal)
      }
      case None =>
        ptf.updateGoal(goal)
    }

  override def toString = "AxiomGenTask(" + plugin + ")"
}
