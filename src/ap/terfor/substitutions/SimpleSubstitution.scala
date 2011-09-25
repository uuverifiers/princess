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

package ap.terfor.substitutions;

import ap.basetypes.IdealInt

import ap.terfor._
import ap.terfor.linearcombination.{LinearCombination,
                                    LinearCombination0, LinearCombination1}
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
