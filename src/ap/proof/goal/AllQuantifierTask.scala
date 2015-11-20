/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
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

  val priority : Int = -5000 + age

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
