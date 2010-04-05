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

import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.substitutions.VariableSubst
import ap.util.{Debug, PlainRange}
import ap.proof.tree.{ProofTree, ProofTreeFactory}

object QuantifierTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
}

abstract class QuantifierTask(_formula : Conjunction, _age : Int)
               extends FormulaTask(_formula, _age) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(QuantifierTask.AC,
                   !formula.isTrue && !formula.isFalse &&
                   !formula.isLiteral && !formula.isNegatedConjunction &&
                   !formula.quans.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
    
  /**
   * The name prefix to use for generated constants
   */
  protected def constantNameBase : String
  
  /**
   * Compute the new set of eliminated constants for a goal, given the set
   * of new constants (when carrying out this task)
   */
  protected def newEliminatedConstants(goal : Goal,
                                       newConstants : Iterable[ConstantTerm])
                                                            : Set[ConstantTerm]
    
                                                            
  protected def instantiateWithConstants(keepThisTask : Boolean,
                                         goal : Goal,
                                         ptf : ProofTreeFactory) : ProofTree = {
    val (quan, num) = firstQuans(formula)
    val constants = for (i <- PlainRange(num))
                    yield new ConstantTerm (constantNameBase + goal.age + "_" + i)

    val newOrder = (goal.order /: constants)((o, c) => o.extend(c, Set.empty))
    val newBindingContext = goal.bindingContext.addAndContract(constants, quan)
    val newConstantFreedom = if (quan == Quantifier.ALL)
                               goal.constantFreedom addTopStatus constants
                             else
                               goal.constantFreedom
    
    val newVocabulary = Vocabulary(newOrder, newBindingContext, newConstantFreedom)
    
    val newElimConstants = newEliminatedConstants(goal, constants)
    
    val instantiatedConj = formula.instantiate(constants)(newOrder)
    val instantiatedConjTask =
      Goal.formulaTasks(instantiatedConj, goal.age,
                        newElimConstants, newVocabulary, goal.settings)

    val thisTask : Iterable[PrioritisedTask] =
      if (keepThisTask) goal.formulaTasks(formula) else List()
    
    val collector = goal.getInferenceCollector
    if (collector.isLogging)
      collector.instantiateQuantifier(formula.negate, constants,
                                      instantiatedConj.negate, newOrder)
    
    ptf.quantify(ptf.updateGoal(newElimConstants,
                                newVocabulary,
                                instantiatedConjTask ++ thisTask,
                                collector.getCollection,
                                goal),
                 quan, constants, goal.vocabulary, newOrder)
  }

  /**
   * Determine the leading quantifier of the conjunction and the number of the
   * same quantifiers in a row
   *
   * TODO: do this in a smarter way (determine which quantifiers can be permuted)?   
   */
  private def firstQuans(f : Conjunction) : (Quantifier, Int) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(QuantifierTask.AC, !f.quans.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
                                                                
    val quans = f.quans
                                                                  
    val quan = quans.last
    val num = quans.size - quans.lastIndexOf(quan.dual) - 1
    (quan, num)
  }                                                            

  val name : String = "QuantifiedFor"

}
