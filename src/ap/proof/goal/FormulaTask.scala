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

import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.util.Debug
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree.{ProofTree, ProofTreeFactory}

object FormulaTask {

  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
}


/**
 * The representation of formulas in a proof goal that are more complex than
 * simple facts. Such formulas are considered to have positive
 * polarity, i.e., as conjunctions in the succedent of a goal.
 * This class is both responsible for storing such formulas and for eventually
 * processing the formulas, e.g. by splitting up the formulas/proof goal.
 */
abstract class FormulaTask(val formula : Conjunction, val age : Int)
         extends PrioritisedTask {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(FormulaTask.AC, isCoveredFormula(formula))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask

  /**
   * Update the task with possibly new information from the goal
   */
  def updateTask(goal : Goal, factCollector : Conjunction => unit)
                                                   : Seq[FormulaTask] = {
    val reducedFormula = goal reduceWithFacts formula
    if (reducedFormula == formula) {
      List(this)
    } else {
      if (Param.PROOF_CONSTRUCTION(goal.settings)) {
        // we cannot really update the task in this case, but we still store
        // the reduced formula to obtain more precise task priorities
        
        constructWrappedTask(reducedFormula, goal)
        
      } else {
        
        if (isCoveredFormula(reducedFormula)) {
          List(this.updateFormula(reducedFormula, goal))
        } else {
          if (AddFactsTask isCoveredFormula reducedFormula) {
            factCollector(reducedFormula)
            List()
          } else {
            goal formulaTasks reducedFormula
          }
        }
        
      }
    }     
  }
  
  protected[goal] def constructWrappedTask(reducedFormula : Conjunction,
                                           goal : Goal) : Seq[FormulaTask] = {
    val simplifiedTasks =
      if (isCoveredFormula(reducedFormula))
        List(this.updateFormula(reducedFormula, goal))
      else
        goal formulaTasks reducedFormula
    if (simplifiedTasks.isEmpty)
      List()
    else
      List(new WrappedFormulaTask (this, simplifiedTasks))
  }
  
  val name : String
   
  override def toString : String = name + "(" + priority + ", " + formula + ")"
   
}
