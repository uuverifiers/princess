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

object IdentitySubst {
  
  def unapply(s : Substitution) : Boolean = s.isInstanceOf[IdentitySubst]
  
}

class IdentitySubst (protected [substitutions] val order : TermOrder)
      extends SimpleSubstitution {

  protected[substitutions] def passQuantifiers(num : Int) : Substitution = this
  
  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = v

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term = c

  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean = true

  //////////////////////////////////////////////////////////////////////////////
  
  def sortBy(newOrder : TermOrder) : IdentitySubst = new IdentitySubst(newOrder)

  override def toString : String = "[]"
  
}
