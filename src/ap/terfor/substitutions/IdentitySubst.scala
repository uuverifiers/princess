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

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}
import ap.terfor.preds.{Atom, PredConj}

object IdentitySubst {
  
  def unapply(s : Substitution) : Boolean = s.isInstanceOf[IdentitySubst]
  
}

class IdentitySubst (protected [substitutions] val order : TermOrder)
      extends Substitution {

  protected[substitutions] def passQuantifiers(num : Int) : Substitution = this
  
  def apply(t : Term) : Term = t

  def apply(lc : LinearCombination) : LinearCombination = lc

  protected[substitutions] def pseudoApply(lc : LinearCombination)
                                          : LinearCombination = lc

  override def apply(f : Formula) : Formula = f
  
  override def apply(conj : EquationConj) : EquationConj = conj

  override def apply(negConj : NegEquationConj) : NegEquationConj = negConj

  override def apply(conj : InEqConj) : InEqConj = conj

  override def apply(conj : ArithConj) : ArithConj =  conj

  override def apply(conj : Conjunction) : Conjunction = conj

  override def apply(conjs : NegatedConjunctions) : NegatedConjunctions = conjs

  override def apply(a : Atom) : Atom = a

  override def apply(conj : PredConj) : PredConj = conj
  
  //////////////////////////////////////////////////////////////////////////////
  
  def sortBy(newOrder : TermOrder) : IdentitySubst = new IdentitySubst(newOrder)

  override def toString : String = "[]"
  
}
