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

package ap.terfor.substitutions;

import ap.terfor.linearcombination.LinearCombination
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
trait SimpleSubstitution extends Substitution {

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term


  /**
   * Simple substitutions work by simple replacement
   */
  def apply(t : Term) : Term = t match {
    case t : VariableTerm => applyToVariable(t)
    case t : ConstantTerm => applyToConstant(t)
    case OneTerm => OneTerm
    case t : LinearCombination => apply(t)
  }
     
  def apply(lc : LinearCombination) : LinearCombination =
    idOrElse(lc,
             LinearCombination(for ((c, t) <- lc.elements)
                               yield (c, apply(t)),
                               order))

  protected[substitutions] def pseudoApply(lc : LinearCombination)
                                            : LinearCombination = apply(lc)

}
