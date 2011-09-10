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

import ap.util.{Debug, Logic}

import ap.terfor._

object VariableSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
}

/**
 * Substitute the variable starting from index <code>offset</code> with the
 * terms in <code>replacements</code>. I.e., <code>VariableTerm(offset)</code>
 * is going to be replaced with <code>replacements(0)</code>, etc. All other
 * variables above <code>offset+replacements.size</code> are shifted downwards
 * by <code>replacements.size</code>
 */
class VariableSubst(offset : Int,
                    replacements : Seq[Term],
                    protected [substitutions] val order : TermOrder)
      extends SimpleSubstitution {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(VariableSubst.AC,
                   (offset >= 0) &&
                   Logic.forall(for (t <- replacements.iterator)
                                yield (order isSortingOf t)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////     

  protected[substitutions] def passQuantifiers(num : Int) : Substitution = {
    // TODO: could be optimised by caching
    val shiftSubst = VariableShiftSubst(0, num, order)
    val newReplacements = for (t <- replacements) yield shiftSubst(t)
    new VariableSubst(offset + num, newReplacements, order)
  }

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = {
    val i = v.index
    if (i < offset)
      v
    else if (i - offset < replacements.size)
      replacements(i - offset)
    else
      VariableTerm(i - replacements.size)
  }

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term = c

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : VariableSubst =
    new VariableSubst(offset,
                      for (t <- replacements) yield (newOrder sort t),
                      newOrder)

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = {
    val strings = for ((t, i) <- replacements.iterator.zipWithIndex)
                  yield ("" + VariableTerm(i+offset) + "|->" + t)
    val substs = if (strings.hasNext)
                   strings.reduceLeft((s1 : String, s2 : String) => s1 + " | " + s2)
                 else
                   ""
    "[" + substs + "]"
  }
}
