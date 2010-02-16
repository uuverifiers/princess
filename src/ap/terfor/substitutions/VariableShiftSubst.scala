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

import ap.util.{Debug, Logic}

object VariableShiftSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def apply(offset : Int, shift : Int, order : TermOrder) =
    new VariableShiftSubst (Array.make(offset, 0), shift, order)
  
  def apply(prefix : Array[Int], defaultShift : Int, order : TermOrder) =
    new VariableShiftSubst (prefix, defaultShift, order)

  /**
   * Create functions for shifting the variables in terms or formulas up or
   * down. This is frequently necessary because of De-Brujin indexes 
   */
  def upShifter[A <: TerFor](shift : Int, order : TermOrder) : (A) => A = {
    val shiftUpSubst = VariableShiftSubst(0, shift, order)
    ((x:A) => shiftUpSubst(x).asInstanceOf[A])
  }
  
  /**
   * Create functions for shifting the variables in terms or formulas up or
   * down. This is frequently necessary because of De-Brujin indexes 
   */
  def downShifter[A <: TerFor](shift : Int, order : TermOrder) = new PartialFunction[A, A] {
    val shiftDownSubst = VariableShiftSubst(shift, -shift, order)
    def isDefinedAt(x : A) : Boolean =
      x.variables forall { case VariableTerm(i) => i >= shift }
    def apply(x : A) : A = shiftDownSubst(x).asInstanceOf[A]
  }
  
}

/**
 * Substitution for renaming variables. The arguments of the substitution
 * is a pair <code>(List[Int], Int)</code> that describes how each
 * variable should be shifted: <code>(List(0, 2, -1), 1)</code> specifies that
 * variable 0 stays the same, variable 1 is increased by 2 (renamed to 3),
 * variable 2 is renamed to 1, and all other variables n are renamed to n+1.
 */
class VariableShiftSubst private (private val prefix : Array[Int],
                                  private val defaultShift : Int,
                                  protected [substitutions] val order : TermOrder)
      extends SimpleSubstitution {

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(VariableShiftSubst.AC,
                   defaultShift + prefix.length >= 0 &&
                   (prefix.elements.zipWithIndex forall {case (i, j) => i + j >= 0}))
  //////////////////////////////////////////////////////////////////////////////

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    new VariableShiftSubst(Array.make(num, 0) ++ prefix, defaultShift, order)

  private def applyToVariable(i : Int) : Int = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(VariableShiftSubst.AC, i >= 0)
    ////////////////////////////////////////////////////////////////////////////
    i + (if (i < prefix.length) prefix(i) else defaultShift)
  }

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = {
    val newIndex = applyToVariable(v.index)
    if (newIndex == v.index) v else VariableTerm(newIndex)
  }

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term = c

  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean =
    t.variables forall { case VariableTerm(i) =>
      (if (i < prefix.length) prefix(i) else defaultShift) == 0
    }

  //////////////////////////////////////////////////////////////////////////////
  
  def compose(that : VariableShiftSubst) : VariableShiftSubst = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(VariableShiftSubst.AC, this.order == that.order)
    ////////////////////////////////////////////////////////////////////////////

    val newPrefix = new scala.collection.mutable.ArrayBuffer[Int]
    for ((o, i) <- that.prefix.elements.zipWithIndex)
      newPrefix += (applyToVariable(i + o) - i)
    for (i <- that.prefix.length until (this.prefix.length - that.defaultShift))
      newPrefix += (applyToVariable(i + that.defaultShift) - i)
    new VariableShiftSubst(newPrefix.toArray,
                           this.defaultShift + that.defaultShift,
                           this.order)
  }

  //////////////////////////////////////////////////////////////////////////////
    
  def sortBy(newOrder : TermOrder) : VariableShiftSubst =
    new VariableShiftSubst(prefix, defaultShift, newOrder)

}