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

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    f.isExactDivisionFormula.isDefined || f.isDivisionFormula.isDefined

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
   * Transform a formula with guarded quantifier into an equivalent formula
   * in which quantifiers can be handled through Skolemisation
   */
  private def splitDivisibility(goal : Goal,
                                ptf : ProofTreeFactory) : ProofTree = {
    implicit val order = goal.order
    
    val newFormula =
      (for ((lc, phi) <- formula.isExactDivisionFormula) yield {
         // then we translate a formula <code> EX ( n*_0 + t = 0 & phi) </code>
         // into
         // <code> ALL ( !(n*_0 + t = 0 > 0 /\ n*_0 + t = 0 < n) &
         //              (n*_0 + t = 0 -> phi)) </code>

         val coeff : IdealInt = lc.leadingCoeff

         //-BEGIN-ASSERTION-////////////////////////////////////////////////////
         Debug.assertInt(DivisibilityTask.AC, coeff.signum > 0)
         //-END-ASSERTION-//////////////////////////////////////////////////////

         val negGuardIneqs =
           InEqConj(Array(lc + IdealInt.MINUS_ONE,
                          lc.scaleAndAdd(IdealInt.MINUS_ONE, coeff - IdealInt.ONE)),
                    order)
         val negGuard =
           Conjunction.negate(negGuardIneqs, order)
      
         val implication =
           Conjunction.implies(EquationConj(lc, order), phi, order)
         
         Conjunction.quantify(List(Quantifier.ALL),
           Conjunction.conj(Array(negGuard, implication), order), order)
      
       }).orElse(
               
       for ((lowerBound, upperBound, phi) <- formula.isDivisionFormula) yield {
         // then we translate a formula
         // <code> EX ( n*_0 + t >= 0 & -n*_0 - t + m >= 0 & phi ) </code>
         // into
         // <code> !EX (n*_0 + t - m - 1 >= 0 & -n*_0 - t + n - 1 >= 0) &
         //        ALL (n*_0 + t >= 0 & -n*_0 - t + m >= 0 -> phi) </code>
       
         val coeff : IdealInt = lowerBound.leadingCoeff
         val diff = ((-upperBound) constantDiff lowerBound).get
       
         //-BEGIN-ASSERTION-////////////////////////////////////////////////////
         Debug.assertInt(DivisibilityTask.AC,
                         coeff.signum > 0 && diff.signum > 0 && diff < coeff)
         //-END-ASSERTION-//////////////////////////////////////////////////////
       
         val negGuardIneqs =
           InEqConj(Array(upperBound.scaleAndAdd(IdealInt.MINUS_ONE,
                                                 IdealInt.MINUS_ONE),
                          lowerBound.scaleAndAdd(IdealInt.MINUS_ONE,
                                                 coeff - IdealInt.ONE)), order)
         val negGuard =
           Conjunction.negate(negGuardIneqs, order)
       
         val implication =
           Conjunction.implies(InEqConj(Array(lowerBound, upperBound), order),
                               phi, order)
      
         Conjunction.quantify(List(Quantifier.ALL),
           Conjunction.conj(Array(negGuard, implication), order), order)

       }).get
     
    val redNewFormula = goal reduceWithFacts newFormula
       
    val collector = goal.getInferenceCollector
    // TODO: log proof steps
      
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
  def isCoveredFormula(f : Conjunction) : Boolean =
    DivisibilityTask isCoveredFormula f

  val name : String = "DivisibilityFor"

}
