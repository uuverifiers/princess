/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.proof._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.substitutions.VariableSubst
import ap.util.{Debug, PlainRange}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.parameters.Param

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
  
  protected def instantiateWithConstants(goal : Goal)
                                        : (Conjunction,
                                           Seq[ConstantTerm],
                                           TermOrder,
                                           BindingContext) = {
    val (quan, num) = firstQuans(formula)
    val constants = for (i <- PlainRange(num))
                    yield new ConstantTerm (constantNameBase + goal.age + "_" +
                       i + "_" +
                       Param.NAME_PROVIDER(goal.settings).uniqueVariableNumber)

    val newOrder = goal.order extend constants.reverse
    val newBindingContext = goal.bindingContext.addAndContract(constants, quan)
    val instantiatedConj = formula.instantiate(constants)(newOrder)
    
    (instantiatedConj, constants, newOrder, newBindingContext)
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
