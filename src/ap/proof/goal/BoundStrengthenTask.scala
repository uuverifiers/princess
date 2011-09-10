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

import ap.proof.tree.{ProofTreeFactory, ProofTree}
import ap.terfor.equations.EquationConj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.util.Debug

object BoundStrengthenTask {
  
  val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
}

/**
 * Task responsible for strengthening the inequalities <code>lc + b1 >= 0</code>
 * and <code>-lc - b2 >= 0</code> to <code>lc + b >= 1</code> and
 * <code>-lc - b2 >= 1</code>, introducing one splinter
 */
class BoundStrengthenTask(lc : LinearCombination, age : Int)
      extends PrioritisedTask {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(BoundStrengthenTask.AC, lc.constant.isZero)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
        
  val priority : Int = lc.size + age
 
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val order = goal.order
    val inEqs = goal.facts.arithConj.inEqs
    
    val lowerBoundEq = (inEqs findLowerBound lc) match {
      case None =>
        Conjunction.TRUE
      case Some(b) =>
        Conjunction.conj(EquationConj(lc.-(LinearCombination(b))(order), order),
                         order)
    }
    
    val upperBoundEq = (inEqs findLowerBound -lc) match {
      case None =>
        Conjunction.TRUE
      case Some(b) =>
        Conjunction.conj(EquationConj(lc.-(LinearCombination(-b))(order), order),
                         order)
    }
    
    val relevantPredicates =
      for (eq <- List(lowerBoundEq, upperBoundEq).distinct;
           if (!eq.isTrue)) yield eq
    
    relevantPredicates match {
      case List() =>
        // the specified linear combination is not relevant for the goal anymore
        ptf.updateGoal(goal)
      case List(eq) => {
        val goal1 = ptf.updateGoal(goal formulaTasks eq.negate, goal)
        val goal2 = ptf.updateGoal(goal formulaTasks eq, goal)
        ptf.and(Array(goal1, goal2), goal.vocabulary)
      }
      case List(eq1, eq2) => {
        val goal1 = ptf.updateGoal(goal formulaTasks eq1.negate, goal)
        val goal2 = ptf.updateGoal(goal formulaTasks eq2.negate, goal)
        val goal3 = ptf.updateGoal(goal formulaTasks
                                     Conjunction.disj(Array(eq1, eq2), order),
                                   goal)
        ptf.and(Array(goal1, goal2, goal3), goal.vocabulary)
      }
    }
  }

  /**
   * Update the task with possibly new information from the goal. If new facts
   * can be derived, these are put into <code>factCollector</code>
   */
  def updateTask(goal : Goal,
                 factCollector : Conjunction => Unit) : Seq[PrioritisedTask] =
    // we do not update anything in this task; if no inequalities for the
    // specified linear combination occur in the goal anymore, we will just
    // ignore the task when it is to be applied
    List(this)

  
  override def toString : String =
    "BoundStrengthenTask(" + priority + ", " + lc  + ")"
}
