/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.substitutions;

import ap.terfor._
import ap.basetypes.IdealInt
import ap.util.Debug

object PseudoConstantSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def unapply(s : Substitution) : Option[(IdealInt, ConstantTerm, Term)] = s match {
    case s : PseudoConstantSubst => Some((s.coeff, s.constant, s.replacement))
    case _ => None
  }
  
}

/**
 * Replace a constant with an arbitrary term
 */
class PseudoConstantSubst(private val coeff : IdealInt,
                          private val constant : ConstantTerm,
                          private val replacement : Term,
                          protected [substitutions] val order : TermOrder)
      extends PseudoDivSubstitution {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PseudoConstantSubst.AC,
                   (order isSortingOf replacement) && !coeff.isZero)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////     

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    new PseudoConstantSubst(coeff,
                            constant,
                            // TODO: could be optimised by caching
                            VariableShiftSubst(0, num, order) (replacement),
                            order)
    
  protected[substitutions] def applyToVariable(v : VariableTerm) : (IdealInt, Term) =
    (IdealInt.ONE, v)

  protected[substitutions] def applyToConstant(c : ConstantTerm) : (IdealInt, Term) =
    if (c == constant) (coeff, replacement) else (IdealInt.ONE, c)

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : PseudoConstantSubst =
    new PseudoConstantSubst(coeff, constant, newOrder sort replacement, newOrder)

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = "[" + coeff + "*" + constant + " |-> " + replacement + "]"

}
