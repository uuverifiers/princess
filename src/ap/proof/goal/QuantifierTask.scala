/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.proof._
import ap.terfor.{ConstantTerm, TermOrder}
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
  
  protected def instantiateWithConstants(goal : Goal)
                                        : (Conjunction,
                                           Seq[ConstantTerm],
                                           TermOrder,
                                           BindingContext) = {
    val (quan, num) = firstQuans(formula)
    val constants = for (i <- PlainRange(num))
                    yield new ConstantTerm (constantNameBase + goal.age + "_" + i)

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
