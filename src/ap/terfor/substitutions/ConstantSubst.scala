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

import ap.util.{Debug, Seqs}
import scala.collection.mutable.HashMap

object ConstantSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def apply(c : ConstantTerm, replacement : Term, order : TermOrder) : ConstantSubst =
    new ConstantSubst(Map((c, replacement)), order)
  
  def apply(replacements : scala.collection.Map[ConstantTerm, Term],
            order : TermOrder) : ConstantSubst =
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

  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean =
    Seqs.disjointSeq(t.constants, replacements.keysIterator)

  //////////////////////////////////////////////////////////////////////////////

  protected[substitutions] def compose(that : ConstantSubst) : ConstantSubst = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConstantSubst.AC, this.order == that.order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newReplacements = new HashMap[ConstantTerm, Term]
    newReplacements ++= this.replacements
    
    for ((c, t) <- that.replacements)
      newReplacements += (c -> this(t))
    
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
