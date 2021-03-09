/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.{Formula, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.substitutions.VariableSubst
import ap.util.{Debug, PlainRange}
import ap.proof.Vocabulary
import ap.proof.tree.{ProofTree, ProofTreeFactory}

object AllQuantifierTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    f.quans.lastOption == Some(Quantifier.ALL)

}

class AllQuantifierTask(_formula : Conjunction, _age : Int)
      extends QuantifierTask(_formula, _age) {

  // add the size of the formula to make behaviour more deterministic
  val priority : Int = -5000 + age + formula.opCount

  protected val constantNameBase : String = "all_"
    
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val (instantiatedConj, constants, newOrder, newBindingContext) =
      instantiateWithConstants(goal)

    val newVocabulary =
      Vocabulary(newOrder, newBindingContext,
                 goal.constantFreedom addTopStatus constants)
    val newElimConstants = goal.eliminatedConstants ++ constants

    val instantiatedConjTask =
      Goal.formulaTasks(instantiatedConj, goal.age,
                        newElimConstants, newVocabulary, goal.settings)

    val collector = goal.getInferenceCollector
    if (collector.isLogging)
      collector.instantiateQuantifier(formula.negate, constants,
                                      instantiatedConj.negate, newOrder)

    ptf.quantify(ptf.updateGoal(newElimConstants,
                                newVocabulary,
                                instantiatedConjTask,
                                collector.getCollection,
                                goal),
                 Quantifier.ALL, constants, goal.vocabulary, newOrder)
  }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new AllQuantifierTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    AllQuantifierTask.isCoveredFormula(f)

}
