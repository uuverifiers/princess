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

import ap.basetypes.IdealInt

import ap.terfor._
import ap.terfor.linearcombination.{LinearCombination,
                                    LinearCombination0, LinearCombination1,
                                    LinearCombination2}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.util.Debug

object SimpleSubstitution {

  private val AC = Debug.AC_SUBSTITUTIONS
  
}

/**
 * A substitution that works by simple replacement of constants or variables
 * with arbitrary terms
 */
abstract class SimpleSubstitution extends Substitution {

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term

  /**
   * Simple substitutions work by simple replacement
   */
  final def apply(t : Term) : Term = t match {
    case t : VariableTerm => applyToVariable(t)
    case t : ConstantTerm => applyToConstant(t)
    case OneTerm => OneTerm
    case t : LinearCombination => apply(t)
  }
     
  final def apply(lc : LinearCombination) : LinearCombination = lc match {
    case lc : LinearCombination0 => {
      lc
    }
    case lc : LinearCombination1 => {
      val leadingTerm = lc.leadingTerm
      val newLeadingTerm = apply(leadingTerm)
      if (leadingTerm eq newLeadingTerm)
        lc
      else
        LinearCombination(lc.leadingCoeff, newLeadingTerm, lc.constant, order)
    }
    case lc : LinearCombination2 => {
      val t0 = lc getTerm 0
      val t1 = lc getTerm 1
      
      val newT0 = apply(t0)
      val newT1 = apply(t1)
      
      if ((t0 eq newT0) && (t1 eq newT1))
        lc
      else
        LinearCombination(Array((lc getCoeff 0, newT0),
                                (lc getCoeff 1, newT1),
                                (lc.constant, OneTerm)),
                          order)
    }
    case _ => {
      val N = lc.size
      val newTerms = new Array[(IdealInt, Term)](N)
    
      var i = 0
      var changed = false
      while (i < N) {
        val t = lc getTerm i
        val newT = apply(t)
        newTerms(i) = (lc getCoeff i, newT)
      
        if (!(newT eq t))
          changed = true
        
        i = i + 1
      }
    
      if (changed)
        LinearCombination(newTerms, order)
      else
        lc
    }
  }

  protected[substitutions] def pseudoApply(lc : LinearCombination)
                                            : LinearCombination = apply(lc)

}
