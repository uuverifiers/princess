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
