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

import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.util.Debug

object ComposeSubsts {
  
  private val AC = Debug.AC_SUBSTITUTIONS

  def apply(substs : Iterable[Substitution], order : TermOrder) : Substitution =
    apply(substs.elements, order)

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

  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean =
    firstSubst.isIdentityOn(t) && secondSubst.isIdentityOn(t)

  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : ComposeSubsts =
    new ComposeSubsts(secondSubst.sortBy(newOrder),
                      firstSubst.sortBy(newOrder),
                      newOrder)
 
  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = "" + secondSubst + " . " + firstSubst

}
