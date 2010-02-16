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
   * a conjunction
   * <code>ALL (n*_0 + t + 1 != 0) /\ ALL (n*_0 + t + 2 != 0) /\ ...</code>
   * in the succedent
   */
  private def splitDivisibility(goal : Goal,
                                ptf : ProofTreeFactory) : ProofTree = {
    val lc = formula.arithConj.positiveEqs(0)
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertInt(DivisibilityTask.AC,
                    !lc.isEmpty && lc.leadingTerm == VariableTerm(0))
    ////////////////////////////////////////////////////////////////////////////

    val coeff : IdealInt = lc.leadingCoeff
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertInt(DivisibilityTask.AC, coeff.signum > 0)
    ////////////////////////////////////////////////////////////////////////////

    val order = goal.order

    val y = LinearCombination(VariableTerm(1), order)
    val newLC = LinearCombination.sum(Array((IdealInt.ONE, lc),
                                            (IdealInt.ONE, y)), order)
    
    val yCond = InEqConj(Array(y + IdealInt.MINUS_ONE,
                               -y + (coeff - IdealInt.ONE)), order)
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
  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new DivisibilityTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean = f.isDivisibility

  val name : String = "DivisibilityFor"

}
