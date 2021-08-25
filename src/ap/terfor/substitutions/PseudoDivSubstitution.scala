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
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.util.Debug

object PseudoDivSubstitution {

  private val AC = Debug.AC_SUBSTITUTIONS
  
}

/**
 * Trait for substitutions that can also replace constants or variables with
 * coefficient, like <code>n * c</code>. This is done through
 * pseudo-division if necessary (and possible)
 */
abstract class PseudoDivSubstitution extends Substitution {

  /**
   * The subclasses can specify both the coefficient of the variable or constant
   * that is supposed to be replaced and the actual replacement. I.e.,
   * for <code>applyToVariable(v)==(n, t)</code> the described substitution is
   * <code> n * v |-> t </code> 
   */
  protected[substitutions] def applyToVariable(v : VariableTerm) : (IdealInt, Term)

  protected[substitutions] def applyToConstant(c : ConstantTerm) : (IdealInt, Term)

  /**
   * Application to terms is not supported, because it would not be possible to
   * do pseudo-division
   */
  def apply(t : Term) : Term =
    throw new UnsupportedOperationException
        
  def apply(lc : LinearCombination) : LinearCombination =
    throw new UnsupportedOperationException

  protected[substitutions] def pseudoApply(lc : LinearCombination) : LinearCombination = {
    // for each term of the linear combination, compute the replacing term and
    // the new rational coefficient in form of two <code>IdealInt</code>s
    val repls = for ((coeff, ter) <- lc.pairSeq) yield {
                  val (replDenom, repl) = ter match {
                    case c : ConstantTerm => applyToConstant(c)
                    case v : VariableTerm => applyToVariable(v)
                    case OneTerm => (IdealInt.ONE, OneTerm)
                  }
       
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(PseudoDivSubstitution.AC, !replDenom.isZero)
                  //-END-ASSERTION-/////////////////////////////////////////////
                         
                  if (replDenom.isOne) {
                    (coeff, IdealInt.ONE, repl)
                  } else {
                    // we return the numerator and the denominator of the
                    // coefficient of the replacing term
                    val gcd = coeff gcd replDenom
                    (coeff / gcd, replDenom / gcd, repl)
                  }
                }
    
    val denomLcm = IdealInt.lcm(for (r <- repls.iterator) yield (r _2))

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(PseudoDivSubstitution.AC, denomLcm.signum > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    LinearCombination(for ((num, denom, repl) <- repls.iterator)
                      yield (num * (denomLcm / denom), repl),
                      order)
  }

}
