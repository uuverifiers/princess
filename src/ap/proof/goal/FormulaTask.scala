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

package ap.proof.goal;

import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.util.Debug
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree.{ProofTree, ProofTreeFactory}

object FormulaTask {

  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
  protected[goal] def isFunctionalityAxiom(formula : Conjunction,
                                           settings : GoalSettings) : Boolean =
    formula.negatedConjs.isEmpty &&
    formula.predConj.negativeLits.isEmpty &&
    (formula.predConj.positiveLits match {
       case Seq(a, b) =>
         a.pred == b.pred &&
         (Param.FUNCTIONAL_PREDICATES(settings) contains a.pred) &&
         a.init == b.init
       case Seq(a) =>
         (Param.FUNCTIONAL_PREDICATES(settings) contains a.pred)
       case _ => false
     })
  
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

  import FormulaTask.isFunctionalityAxiom

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask

  /**
   * Update the task with possibly new information from the goal
   */
  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[FormulaTask] = {
    val reducedFormula = goal.reduceWithFacts.tentativeReduce(formula)
    if (reducedFormula eq formula) {
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

    if (simplifiedTasks.isEmpty) {
      if (isFunctionalityAxiom(formula, goal.settings))
        // we have to be careful to not remove functionality axioms,
        // since those might be reduced to false during reduction
        List(this)
      else
        List()
    } else {
      List(new WrappedFormulaTask (this, simplifiedTasks))
    }
  }

  val name : String
   
  override def toString : String = name + "(" + priority + ", " + formula + ")"
   
}
