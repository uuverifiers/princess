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
import ap.terfor.arithconj.ArithConj
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}
import ap.terfor.preds.{Atom, PredConj}
import ap.util.Debug

object Substitution {

  private val AC = Debug.AC_SUBSTITUTIONS
  
}

/**
 * A substitution is a mapping from <code>TerFor</code> to <code>TerFor</code>
 * that replaces variables and constants with arbitrary other terms. It is
 * required that a substitution is only applied to terms/formulas that are
 * sorted according to <code>order</code>. There are two more concrete
 * sub-traits: <code>SimpleSubstitution</code>, which performs a simple
 * replacement of constants or variables, and <code>PseudoDivSubstitution</code>,
 * which can make use of pseudo-division in order to replace expressions
 * <code>n * c</code>.
 */
trait Substitution extends ((TerFor) => TerFor) with Sorted[Substitution] {

  /**
   * The term order that is used for the resulting terms or formulas. We require
   * that a substitution is only applied to terms/formulas that are already
   * sorted according to this order
   */
  protected[substitutions] def order : TermOrder
  
  /**
   * Substitution that is to be used underneath <code>num</code> quantifiers.
   * Because we use De Bruijn indexes, passing quantifiers shifts the variables
   * in a substitution
   */
  protected[substitutions] def passQuantifiers(num : Int) : Substitution
  
  /**
   * For performance reasons, a <code>Substitution</code> can tell whether
   * it is possible at all its application will change a term or a formula. This
   * can be found out by looking at the free variables in an expression, for
   * instance. In this case, this method has to return <code>false</code>.
   */
  protected[substitutions] def isIdentityOn(t : TerFor) : Boolean

  protected def idOrElse[A <: TerFor](t : A, otherwise : => A) : A = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(Substitution.AC, order isSortingOf t)
    ////////////////////////////////////////////////////////////////////////////     
     
    if (isIdentityOn(t)) t else otherwise     
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Compare the order of this <code>Substitution</code> with a given order. We
   * use equality here, because the behaviour would be quite confusing with
   * the relation <code>isSubOrderOf</code> (remember that the substitution has
   * to cope with arbitrary terms/formulas that are sorted by the order) 
   */
  def isSortedBy(otherOrder : TermOrder) : Boolean = (order == otherOrder)

  //////////////////////////////////////////////////////////////////////////////
  
  def apply(t : TerFor) : TerFor = {
    t match {
    case t : Term => apply(t)
    case f : Formula => apply(f)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // The following methods are implemented in the sub-traits
    
  def apply(t : Term) : Term

  def apply(lc : LinearCombination) : LinearCombination

  /**
   * Some kinds of substitutions can only be applied when pseudo-reduction
   * is allowed to be performed. Implementations of the following method are
   * allowed to multiply <code>lc</code> with arbitrary positive integers to
   * achieve this.
   */
  protected[substitutions] def pseudoApply(lc : LinearCombination) : LinearCombination

  //////////////////////////////////////////////////////////////////////////////
  
  def apply(f : Formula) : Formula = {
    f match {
    case f : EquationConj => apply(f)
    case f : NegEquationConj => apply(f)
    case f : InEqConj => apply(f)
    case f : ArithConj => apply(f)
    case f : Conjunction => apply(f)
    case f : NegatedConjunctions => apply(f)
    case f : Atom => apply(f)
    case f : PredConj => apply(f)
    }
  }
  
  def apply(conj : EquationConj) : EquationConj =
    idOrElse(conj,
             EquationConj(for (lc <- conj.elements) yield pseudoApply(lc), order))
                                    
  def apply(negConj : NegEquationConj) : NegEquationConj =
    idOrElse(negConj,
             NegEquationConj(for (lc <- negConj.elements) yield pseudoApply(lc), order))

  def apply(conj : InEqConj) : InEqConj =
    idOrElse(conj,
             InEqConj(for (lc <- conj.elements) yield pseudoApply(lc), order))

  def apply(conj : ArithConj) : ArithConj =
    idOrElse(conj,
             ArithConj(apply(conj.positiveEqs),
                       apply(conj.negativeEqs),
                       apply(conj.inEqs),
                       order))

  def apply(conj : Conjunction) : Conjunction =
    idOrElse(conj,
             {
               val pastSubst = this.passQuantifiers(conj.quans.size)
               Conjunction(conj.quans,
                           pastSubst(conj.arithConj),
                           pastSubst(conj.predConj),
                           pastSubst(conj.negatedConjs),
                           order)
             })

  def apply(conjs : NegatedConjunctions) : NegatedConjunctions =
    idOrElse(conjs,
             NegatedConjunctions(for (conj <- conjs) yield apply(conj), order))

  def apply(a : Atom) : Atom =
    idOrElse(a,
             a.updateArgs(for (lc <- a) yield apply(lc))(order))

  def apply(conj : PredConj) : PredConj =
    idOrElse(conj,
             conj.updateLits(for (a <- conj.positiveLits) yield apply(a),
                             for (a <- conj.negativeLits) yield apply(a))
                            (order))
}
