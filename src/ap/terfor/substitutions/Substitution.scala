/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import ap.terfor._
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
abstract class Substitution extends ((TerFor) => TerFor) with Sorted[Substitution] {

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
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Compare the order of this <code>Substitution</code> with a given order. We
   * use equality here, because the behaviour would be quite confusing with
   * the relation <code>isSubOrderOf</code> (remember that the substitution has
   * to cope with arbitrary terms/formulas that are sorted by the order) 
   */
  final def isSortedBy(otherOrder : TermOrder) : Boolean = (order == otherOrder)

  //////////////////////////////////////////////////////////////////////////////
  
  final def apply(t : TerFor) : TerFor = t match {
    case t : Term => apply(t)
    case f : Formula => apply(f)
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
  // Functions for recursively applying a substitution
  // rather low-level code, to avoid overhead and too many dynamic dispatches
  
  def apply(f : Formula) : Formula = f match {
    case f : EquationConj => apply(f)
    case f : NegEquationConj => apply(f)
    case f : InEqConj => apply(f)
    case f : ArithConj => apply(f)
    case f : Conjunction => apply(f)
    case f : NegatedConjunctions => apply(f)
    case f : Atom => apply(f)
    case f : PredConj => apply(f)
  }
  
  private def recPseudoApply(lcs : Seq[LinearCombination])
                            : Option[Seq[LinearCombination]] = {
    val N = lcs.size
    val newLCs = new Array[LinearCombination](N)
    
    var i = 0
    var changed = false
    while (i < N) {
      val lc = lcs(i)
      val newLC = pseudoApply(lc)
      newLCs(i) = newLC
      
      if (!(newLC eq lc))
        changed = true
        
      i = i + 1
    }
    
    if (changed) Some(newLCs) else None
  }
  
  def apply(conj : EquationConj) : EquationConj =
    recPseudoApply(conj) match {
      case Some(newLCs) => EquationConj(newLCs, order)
      case None => conj
    }

  def apply(negConj : NegEquationConj) : NegEquationConj =
    recPseudoApply(negConj) match {
      case Some(newLCs) => NegEquationConj(newLCs, order)
      case None => negConj
    }

  def apply(conj : InEqConj) : InEqConj =
    recPseudoApply(conj) match {
      case Some(newLCs) => InEqConj(newLCs, order)
      case None => conj
    }

  def apply(conj : ArithConj) : ArithConj = {
    val posEqs = conj.positiveEqs
    val negEqs = conj.negativeEqs
    val inEqs = conj.inEqs
    
    val newPosEqs = apply(posEqs)
    val newNegEqs = apply(negEqs)
    val newInEqs = apply(inEqs)
    
    if ((posEqs eq newPosEqs) && (negEqs eq newNegEqs) && (inEqs eq newInEqs))
      conj
    else
      ArithConj(newPosEqs, newNegEqs, newInEqs, order)
  }

  def apply(conj : Conjunction) : Conjunction = {
    val pastSubst = this.passQuantifiers(conj.quans.size)
    
    val arithConj = conj.arithConj
    val predConj = conj.predConj
    val negConjs = conj.negatedConjs
    
    val newArithConj = pastSubst(arithConj)
    val newPredConj = pastSubst(predConj)
    val newNegConjs = pastSubst(negConjs)

    if ((arithConj eq newArithConj) &&
        (predConj eq newPredConj) &&
        (negConjs eq newNegConjs))
      conj
    else
      Conjunction(conj.quans, newArithConj, newPredConj, newNegConjs, order)
  }

  def apply(conjs : NegatedConjunctions) : NegatedConjunctions = {
    val N = conjs.size
    val newConjs = new Array[Conjunction](N)
    
    var i = 0
    var changed = false
    while (i < N) {
      val c = conjs(i)
      val newC = apply(c)
      newConjs(i) = newC
      
      if (!(newC eq c))
        changed = true
        
      i = i + 1
    }

    if (changed)
      NegatedConjunctions(newConjs, order)
    else
      conjs
  }

  def apply(a : Atom) : Atom = {
    val N = a.size
    val newLCs = new Array[LinearCombination](N)
    
    var i = 0
    var changed = false
    while (i < N) {
      val lc = a(i)
      val newLC = apply(lc)
      newLCs(i) = newLC
      
      if (!(newLC eq lc))
        changed = true
        
      i = i + 1
    }

    if (changed)
      Atom.createNoCopy(a.pred, newLCs, order)
    else
      a
  }

  private def recApply(atoms : Seq[Atom]) : Option[Seq[Atom]] = {
    val N = atoms.size
    val newAtoms = new Array[Atom](N)
    
    var i = 0
    var changed = false
    while (i < N) {
      val a = atoms(i)
      val newA = apply(a)
      newAtoms(i) = newA
      
      if (!(newA eq a))
        changed = true
        
      i = i + 1
    }
    
    if (changed) Some(newAtoms) else None
  }

  def apply(conj : PredConj) : PredConj =
    (recApply(conj.positiveLits), recApply(conj.negativeLits)) match {
      case (Some(newPosLits), Some(newNegLits)) =>
        PredConj(newPosLits, newNegLits, order) 
      case (Some(newPosLits), _) =>
        PredConj(newPosLits, conj.negativeLits, order) 
      case (_, Some(newNegLits)) =>
        PredConj(conj.positiveLits, newNegLits, order) 
      case _ => conj
    }
}
