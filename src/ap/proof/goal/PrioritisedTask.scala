/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal;

import ap.terfor.conjunctions.Conjunction

/**
 * Trait for tasks that are 
 * given a <code>priority</code>, based on the age (to ensure fairness)
 * and on other criteria to work at different tasks in a meaningful order.
 * Tasks with smaller <code>priority</code> are supposed to be handled first.
 * Proof tasks of this kind cannot fail, i.e., the result of <code>apply</code>
 * is simply <code>ProofTree</code>.
 */
trait PrioritisedTask extends Task {

  val priority : Int
 
  /**
   * Update the task with possibly new information from the goal. If new facts
   * can be derived, these are put into <code>factCollector</code>
   */
  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[PrioritisedTask]
  
}
