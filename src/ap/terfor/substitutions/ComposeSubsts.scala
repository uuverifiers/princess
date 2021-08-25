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
import ap.util.Debug

object ComposeSubsts {
  
  private val AC = Debug.AC_SUBSTITUTIONS

  def apply(substs : Iterable[Substitution], order : TermOrder) : Substitution =
    apply(substs.iterator, order)

  def apply(substs : Iterator[Substitution], order : TermOrder) : Substitution =
    (new IdentitySubst (order).asInstanceOf[Substitution] /: substs)(
      (combination, subst) => apply(combination, subst, order))
  
  def apply(secondSubst : Substitution,
            firstSubst : Substitution,
            order : TermOrder) : Substitution = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // a sufficient, but not a necessary condition for getting the composed
    // substitution work correctly. This could be weakened
    Debug.assertPre(AC,
                    firstSubst.order == order && secondSubst.order == order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    (secondSubst, firstSubst) match {
      case (_, _ : IdentitySubst) =>
        secondSubst
      case (_ : IdentitySubst, _) =>
        firstSubst
      case (secondSubst : ConstantSubst, firstSubst : ConstantSubst) =>
        // we can parallelise the two substitutions
        secondSubst compose firstSubst
      case (secondSubst : VariableShiftSubst, firstSubst : VariableShiftSubst) =>
        // we can parallelise the two substitutions
        secondSubst compose firstSubst
      case _ =>
        new ComposeSubsts(secondSubst, firstSubst, order)
    }
  }
  
  def unapply(s : Substitution) : Option[(Substitution, Substitution)] = s match {
    case s : ComposeSubsts => Some((s.secondSubst, s.firstSubst))
    case _ => None
  }
}

/**
 * Function composition for two substitutions
 */
class ComposeSubsts private (private val secondSubst : Substitution,
                             private val firstSubst : Substitution,
                             protected [substitutions] val order : TermOrder)
      extends Substitution {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // a sufficient, but not a necessary condition for getting the composed
  // substitution work correctly. This could be weakened
  Debug.assertCtor(ComposeSubsts.AC,
                   firstSubst.order == order && secondSubst.order == order)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  protected[substitutions] def passQuantifiers(num : Int) : Substitution =
    new ComposeSubsts (secondSubst.passQuantifiers(num),
                       firstSubst.passQuantifiers(num),
                       order)
   
  /**
   * For composition, we simply first apply the first substitution and then
   * the second
   */
  def apply(t : Term) : Term =
    secondSubst(firstSubst(t))
     
  def apply(lc : LinearCombination) : LinearCombination =
    secondSubst(firstSubst(lc))

  def pseudoApply(lc : LinearCombination) : LinearCombination =
    secondSubst pseudoApply (firstSubst pseudoApply lc)

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : ComposeSubsts =
    new ComposeSubsts(secondSubst.sortBy(newOrder),
                      firstSubst.sortBy(newOrder),
                      newOrder)
 
  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = "" + secondSubst + " . " + firstSubst

}
