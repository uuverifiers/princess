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

import ap.basetypes.IdealInt
import ap.terfor.{Formula, ConstantTerm, VariableTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, NegatedConjunctions}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.util.{Debug, PlainRange, Seqs}
import ap.parameters.Param
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.BranchInferenceCollector

import scala.collection.mutable.ArrayBuffer

object DivisibilityTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
}

class DivisibilityTask(_formula : Conjunction, _age : Int)
      extends FormulaTask(_formula, _age) {

  val priority : Int = -5000 + age

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    if (!Seqs.disjoint(goal.eliminatedConstants, formula.constants)) {
      splitDivisibility(goal, ptf)
    } else {
      // we just add the formula as a clause to the goal
      ptf.updateGoalAddQFClause(formula, goal)
    }

  /**
   * Transform a formula <code>EX (n*_0 + t = 0)</code> in the succedent into
   * a formula
   * <code>!EX EX (n*_1 + t + _0 = 0 /\ _0 > 0 /\ _0 < n)</code>
   * in the succedent
   */
  private def splitDivisibility(goal : Goal,
                                ptf : ProofTreeFactory) : ProofTree = {
    val lc = formula.arithConj.positiveEqs(0)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(DivisibilityTask.AC,
                    !lc.isEmpty && lc.leadingTerm == VariableTerm._0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val coeff : IdealInt = lc.leadingCoeff
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(DivisibilityTask.AC, coeff.signum > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    implicit val order = goal.order

    val y = LinearCombination(VariableTerm(1), order)
    val newLC = lc + y
    
    val yCond =
      InEqConj(Array(y + IdealInt.MINUS_ONE,
                     y.scaleAndAdd(IdealInt.MINUS_ONE, coeff - IdealInt.ONE)), order)
    val newEq = EquationConj(newLC, order)
    
    val newMatrix = Conjunction.conj(Array(yCond, newEq), order)
    val newFormula = Conjunction.quantify(Array(Quantifier.EX, Quantifier.EX),
                                          newMatrix, order).negate
    
    val collector = goal.getInferenceCollector
    if (collector.isLogging)
      collector.divRight(formula.negate, newFormula.negate, order)
    
    ptf.updateGoal(goal.formulaTasks(newFormula), collector.getCollection, goal)
  }
    
  /**
   * Determine whether this formula requires real splitting, or whether it can
   * be passed to the constraint unchanged
   */
  def splittingNecessary(goal : Goal) : Boolean =
    !Seqs.disjoint(goal.eliminatedConstants, formula.constants) &&
    formula.isProperDivisibility
  
  /*
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new DivisibilityTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean = f.isDivisibility

  val name : String = "DivisibilityFor"

}
