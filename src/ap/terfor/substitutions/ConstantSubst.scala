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

import ap.util.{Debug, Seqs}
import scala.collection.mutable.HashMap

object ConstantSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def apply(c : ConstantTerm, replacement : Term, order : TermOrder) : ConstantSubst =
    new ConstantSubst(Map((c, replacement)), order)
  
  def apply(replacements : scala.collection.Map[ConstantTerm, Term],
            order : TermOrder) : Substitution =
    if (replacements.isEmpty)
      new IdentitySubst (order)
    else
      new ConstantSubst(replacements, order)
  
}

/**
 * Replace a constant with an arbitrary term
 */
class ConstantSubst private
                    (private val replacements : scala.collection.Map[ConstantTerm, Term],
                     protected [substitutions] val order : TermOrder)
      extends SimpleSubstitution {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ConstantSubst.AC,
                   replacements.valuesIterator forall (order isSortingOf _))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////     

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    if (num == 0) {
      this
    } else {
      val shifter = VariableShiftSubst(0, num, order)
      val newReplacements = new HashMap[ConstantTerm, Term]
      for ((c, t) <- replacements)
        newReplacements += (c -> shifter(t))
      // TODO: could be optimised by caching
      new ConstantSubst(newReplacements, order)
    }

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = v

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term =
    replacements.getOrElse(c, c)

  //////////////////////////////////////////////////////////////////////////////

  protected[substitutions] def compose(that : ConstantSubst) : ConstantSubst = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConstantSubst.AC, this.order == that.order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newReplacements = new HashMap[ConstantTerm, Term]
    newReplacements ++= this.replacements
    
    for ((c, t) <- that.replacements)
      newReplacements.put(c, this(t))
    
    new ConstantSubst(newReplacements, order)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : ConstantSubst = {
    val newReplacements = new HashMap[ConstantTerm, Term]
    for ((c, t) <- replacements)
      newReplacements += (c -> (newOrder sort t))
    new ConstantSubst(newReplacements, newOrder)
  }

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String =
    "[" + ((for ((c, t) <- replacements) yield ("" + c + " |-> " + t)) mkString ", ")

}
