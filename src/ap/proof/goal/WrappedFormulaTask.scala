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

package ap.proof.goal

import ap.parameters.Param
import ap.proof.tree.{ProofTreeFactory, ProofTree}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, Seqs}

object WrappedFormulaTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK

  object MaybeWrapped {
    def unapply(t : Task) = Some(unwrapReal(t))
  }
  
  def unwrapReal(t : Task) : Task = t match {
    case WrappedFormulaTask(realTask, _) => realTask
    case _ => t
  }
  
}

/**
 * Wrapper class for formula tasks. This is used to handle (theory) propagation
 * when extracting certificates: in this case, all simplifications and
 * reductions have to be done using the basic calculus rules. Reduction of
 * formulae is still used to identify formulae that can be simplified a lot,
 * so that priorities can be chosed in a meaningful way.
 */
case class WrappedFormulaTask(realTask : FormulaTask, simplifiedTasks : Seq[FormulaTask])
           extends FormulaTask(realTask.formula, realTask.age) {

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(WrappedFormulaTask.AC, !simplifiedTasks.isEmpty)
  //////////////////////////////////////////////////////////////////////////////
        
  val priority : Int =
    // we use the mean of the real priority and the simplified task priority
    // (this can boost certain expensive tasks, in particular the
    // BetaFormulaTask)
    (Seqs.min(for (t <- simplifiedTasks.elements) yield t.priority) +
       realTask.priority) / 2

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    realTask(goal, ptf)

  /**
   * Update the task with possibly new information from the goal
   */
  override def updateTask(goal : Goal, factCollector : Conjunction => unit)
                                                   : Seq[FormulaTask] = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertCtor(WrappedFormulaTask.AC, Param.PROOF_CONSTRUCTION(goal.settings))
    ////////////////////////////////////////////////////////////////////////////
    
    simplifiedTasks match {
      case Seq(simpTask) => {
        // if there is only a single simplified task, we continue with the
        // reduced formula

        val reducedFormula = goal reduceWithFacts simpTask.formula
        if (reducedFormula == simpTask.formula)
          List(this)
        else
          realTask.constructWrappedTask(reducedFormula, goal)
      }
      case _ => realTask.updateTask(goal, factCollector)
    }
  }

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    realTask isCoveredFormula f

  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    throw new UnsupportedOperationException

  val name : String = realTask.name

  override def toString : String =
    name + "(" + priority + " <- " + realTask.priority + ", " + formula + ")"

}
