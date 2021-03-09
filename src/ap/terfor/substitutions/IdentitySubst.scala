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
