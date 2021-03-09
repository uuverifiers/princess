/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(WrappedFormulaTask.AC, !simplifiedTasks.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
        
  val priority : Int =
    // we use the mean of the real priority and the simplified task priority
    // (this can boost certain expensive tasks, in particular the
    // BetaFormulaTask)
    (Seqs.min(for (t <- simplifiedTasks.iterator) yield t.priority) +
       realTask.priority) / 2

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    realTask(goal, ptf)

  /**
   * Update the task with possibly new information from the goal
   */
  override def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[FormulaTask] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(WrappedFormulaTask.AC,
                     Param.PROOF_CONSTRUCTION(goal.settings))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // Reduce the simplified tasks, instead of reducing the original
    // formula again

    var changed = false
    val newSimplifiedTasks =
      for (t <- simplifiedTasks;
           newT <- {
             val reducedFormula =
               goal.reduceWithFacts.tentativeReduce(t.formula)
             if (reducedFormula eq t.formula) {
               List(t)
             } else {
               changed = true
               if (t isCoveredFormula reducedFormula)
                 List(t.updateFormula(reducedFormula, goal))
               else
                 goal formulaTasks reducedFormula
             }
           })
      yield newT

    if (changed) {
      if (newSimplifiedTasks.isEmpty) {
        if (FormulaTask.isFunctionalityAxiom(formula, goal.settings))
          // we have to be careful to not remove functionality axioms,
          // since those might be reduced to false during reduction
          return List(this)
        else
          List()
      } else {
        List(new WrappedFormulaTask (realTask, newSimplifiedTasks))
      }
    } else {
      List(this)
    }
  }

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    realTask isCoveredFormula f

  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    throw new UnsupportedOperationException

  val name : String = realTask.name

  override def toString : String =
    name + "(" + priority + " <- " + realTask.priority + ", " + formula + ")"

}
