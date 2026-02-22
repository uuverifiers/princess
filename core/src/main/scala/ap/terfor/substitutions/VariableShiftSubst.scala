/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.util.{Debug, Logic}

object VariableShiftSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def apply(offset : Int, shift : Int, order : TermOrder) =
    new VariableShiftSubst (Array.fill(offset){0}, shift, order)
  
  def apply(prefix : Seq[Int], defaultShift : Int, order : TermOrder) =
    new VariableShiftSubst (prefix.toArray, defaultShift, order)

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

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(VariableShiftSubst.AC,
                   defaultShift + prefix.length >= 0 &&
                   (prefix.iterator.zipWithIndex forall {case (i, j) => i + j >= 0}))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    new VariableShiftSubst(Array.fill(num){0} ++ prefix, defaultShift, order)

  private def applyToVariable(i : Int) : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(VariableShiftSubst.AC, i >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    i + (if (i < prefix.length) prefix(i) else defaultShift)
  }

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = {
    val newIndex = applyToVariable(v.index)
    if (newIndex == v.index) v else VariableTerm(newIndex)
  }

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term = c

  //////////////////////////////////////////////////////////////////////////////
  
  def compose(that : VariableShiftSubst) : VariableShiftSubst = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(VariableShiftSubst.AC, this.order == that.order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newPrefix = new scala.collection.mutable.ArrayBuffer[Int]
    for ((o, i) <- that.prefix.iterator.zipWithIndex)
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
