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

  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean =
    !(t.constants contains constant)

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : PseudoConstantSubst =
    new PseudoConstantSubst(coeff, constant, newOrder sort replacement, newOrder)

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = "[" + coeff + "*" + constant + " |-> " + replacement + "]"

}
