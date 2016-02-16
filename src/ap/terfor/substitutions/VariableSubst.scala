/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.terfor.substitutions;

import ap.util.{Debug, Logic, Seqs}

import ap.terfor._

object VariableSubst {
  
  private val AC = Debug.AC_SUBSTITUTIONS
  
  def apply(offset : Int,
            replacements : Seq[Term],
            order : TermOrder) =
    new VariableSubst(offset, replacements, order, null)

  private class LazyVariableSubst(subst : VariableSubst, shift : Int) {
    lazy val newSubst = {
      val shiftSubst = VariableShiftSubst(0, shift, subst.order)
      val newReplacements = for (t <- subst.replacements) yield shiftSubst(t)
      new VariableSubst(subst.offset + shift, newReplacements, subst.order,
                        subst.shiftedSubstCache drop shift)
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Substitute the variable starting from index <code>offset</code> with the
 * terms in <code>replacements</code>. I.e., <code>VariableTerm(offset)</code>
 * is going to be replaced with <code>replacements(0)</code>, etc. All other
 * variables above <code>offset+replacements.size</code> are shifted downwards
 * by <code>replacements.size</code>
 */
class VariableSubst private (
        private val offset : Int,
        private val replacements : Seq[Term],
        protected [substitutions] val order : TermOrder,
        oldSubstCache : Stream[VariableSubst.LazyVariableSubst])
      extends SimpleSubstitution {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(VariableSubst.AC,
                   (offset >= 0) &&
                   Logic.forall(for (t <- replacements.iterator)
                                yield (order isSortingOf t)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////     

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    if (num == 0)
      this
    else
      shiftedSubstCache(num - 1).newSubst

  private val shiftedSubstCache : Stream[VariableSubst.LazyVariableSubst] =
    oldSubstCache match {
      case null =>
        Seqs.toStream { i => new VariableSubst.LazyVariableSubst(this, i + 1) }
      case c =>
        c
    }

  protected[substitutions] def applyToVariable(v : VariableTerm) : Term = {
    val i = v.index
    if (i < offset)
      v
    else if (i - offset < replacementsSize)
      replacements(i - offset)
    else
      VariableTerm(i - replacementsSize)
  }

  private val replacementsSize = replacements.size

  protected[substitutions] def applyToConstant(c : ConstantTerm) : Term = c

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : VariableSubst =
    new VariableSubst(offset,
                      for (t <- replacements) yield (newOrder sort t),
                      newOrder,
                      null)

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
