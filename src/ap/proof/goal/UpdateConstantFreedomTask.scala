/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.proof._
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.terfor.conjunctions.Conjunction

class UpdateConstantFreedomTask(newConstantFreedom : ConstantFreedom,
                                age : Int) extends PrioritisedTask {

  val priority : Int = -40000 + age
  
  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                : Seq[PrioritisedTask] = List(this)

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val (newTasks, newCompoundFormulas) =
      goal.compoundFormulas.updateConstantFreedom(newConstantFreedom, goal)
    val updatedVocabulary = goal.vocabulary updateConstantFreedom newConstantFreedom

    ptf.updateGoal(newCompoundFormulas, newTasks, updatedVocabulary, goal)
  }
  
  override def toString = "UpdateConstantFreedomTask(" + priority + ")"
}
