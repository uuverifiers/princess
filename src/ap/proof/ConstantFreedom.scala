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

package ap.proof

import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Logic, FilterIt, Seqs}

object ConstantFreedom {
  
  private val AC = Debug.AC_CONSTANT_FREEDOM
  
  abstract class ConstantStatus extends PartiallyOrdered[ConstantStatus] {
    def meet(that : ConstantStatus) : ConstantStatus =
      if (this <= that) this else that

    def tryCompareTo[B >: ConstantStatus <% PartiallyOrdered[B]](that : B)
                                                               : Option[Int] =
      (this, that) match {
        case (NonFree, ShieldingEquations) => Some(-1)
        case (ShieldingEquations, NonFree) => Some(1)
        case _ => Some(0) // then this == that
      }
  }
  
  case object NonFree extends ConstantStatus
  case object ShieldingEquations extends ConstantStatus
  
  val BOTTOM = new ConstantFreedom (Map() withDefaultValue NonFree)
  
}

/**
 * Class to represent the set of constants that are considered as "free" (i.e.,
 * that are only unifiable with themselves). Objects of this class are stored
 * in the nodes of proof tree and are updated when the proof is expanded in
 * order to eventually reach a fixed point.
 * 
 * TODO: avoid the creation of new objects whenever possible
 */
class ConstantFreedom private (private val constantStatus :
                                 Map[ConstantTerm, ConstantFreedom.ConstantStatus])
      extends PartiallyOrdered[ConstantFreedom] {

  import ConstantFreedom.{NonFree, ShieldingEquations, ConstantStatus}
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // The status map only explicitly mentions the free constants. All other
  // constants are supposed to be mapped to NonFree by the default-method
  // of the map
  Debug.assertCtor(ConstantFreedom.AC,
                   !(constantStatus.valuesIterator contains NonFree) &&
                   constantStatus(new ConstantTerm ("X")) == NonFree)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  override def <=[B >: ConstantFreedom <% PartiallyOrdered[B]](that : B) : Boolean =
    that match {
      case that : ConstantFreedom =>
        this.constantStatus.size <= that.constantStatus.size &&
        Logic.forall(for ((c, s) <- this.constantStatus.iterator)
                     yield (s <= that.constantStatus(c)))
      case _ => false
    }
    
  def tryCompareTo[B >: ConstantFreedom <% PartiallyOrdered[B]](that : B)
                                                              : Option[Int] =
    that match {
      case that : ConstantFreedom => if (this == that)
                                       Some(0)
                                     else if (this <= that)
                                       Some(-1)
                                     else if (that <= this)
                                       Some(1)
                                     else
                                       None
      case _ => None
    }

  def isBottom : Boolean = constantStatus.isEmpty
                            
  def isBottomWRT(constants : Set[ConstantTerm]) : Boolean =
    Seqs.disjointSeq(constants, constantStatus.keysIterator)
  
  def meet(that : ConstantFreedom) : ConstantFreedom = {
    var newStatus = this.constantStatus
    for ((c, s) <- this.constantStatus) {
      (s meet that.constantStatus(c)) match {
        case NonFree => newStatus = newStatus - c
        case newS if (newS != s) => newStatus = newStatus + (c -> newS)
        case _ => // nothing
      }
    }
    new ConstantFreedom(newStatus)
  }

  /**
   * Set the status of the given constants to the top value (as free as possible)
   */
  def addTopStatus(consts : Iterable[ConstantTerm]) : ConstantFreedom =
    new ConstantFreedom(this.constantStatus ++
                        (for (c <- consts.iterator) yield (c -> ShieldingEquations)))
  
  def --(consts : Iterable[ConstantTerm]) : ConstantFreedom =
    new ConstantFreedom(this.constantStatus -- consts)
  
  /**
   * Given a constraint from which all shielded parts have been removed,
   * determine which constants have to be considered as non-free
   */
  def findNonFreeness(unshieldedConj : Conjunction, bc : BindingContext) : ConstantFreedom =
    new ConstantFreedom(this.constantStatus -- unshieldedConj.constants)
  
  /**
   * List all constants whose status is different in <code>this</code> and
   * <code>that</code>
   */
  def changedConstants(that : ConstantFreedom) : Set[ConstantTerm] =
    (Set() ++ this.constantStatus.keySet ++ that.constantStatus.keySet)
             .filter ((c) => this.constantStatus(c) != that.constantStatus(c))
    
  //////////////////////////////////////////////////////////////////////////////
                                                              
  override def equals(that : Any) : Boolean =
    that match {
      case that : ConstantFreedom => this.constantStatus == that.constantStatus
      case _ => false
    }
  
  override def hashCode : Int = this.constantStatus.hashCode
  
  override def toString : String = this.constantStatus.toString
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Determine whether <code>c</code> is a formula of the shape
   * <code> a*x + t = 0 & phi </code>, where <code>a != 0</code> and
   * <code>x</code> is a quasi-universal constant that is maximal in
   * <code> a*x + t = 0 </code>.
   */
  def isShielded(c : Conjunction, bc : BindingContext) : Boolean =
    (c.arithConj.positiveEqs exists (isShieldingLC(_, bc))) ||
    (c.arithConj.inEqs.equalityInfs exists (isShieldingLC(_, bc))) ||
    (c.negatedConjs exists (nc => nc.iterator forall (isShieldedNeg(_, bc))))
  
  /**
   * Determine whether the formula <code>lc1 - lc2 = 0 & phi</code> is shielded
   * (for arbitrary <code>phi</code>)
   */
  def diffIsShieldingLC(lc1 : LinearCombination, lc2 : LinearCombination,
                        bc : BindingContext) : Boolean =  
    lc1.variables.isEmpty && lc2.variables.isEmpty && {
      val remainingConsts =
        (lc1.constants ++ lc2.constants) filter ((c) => (lc1 get c) != (lc2 get c))
      ((bc maximumConstants remainingConsts) exists (constantStatus(_) != NonFree))
    }
  
  private def isShieldingLC(lc : LinearCombination, bc : BindingContext) : Boolean =
    lc.variables.isEmpty &&
    ((bc maximumConstants lc.constants) exists (constantStatus(_) != NonFree))

  private def isShieldedNeg(c : Conjunction, bc : BindingContext) : Boolean =
    isShielded(c.negate, bc)

  /**
   * Determine the (disjunctively connected) unshielded part of a formula
   */
  def unshieldedPart(c : Conjunction, bc : BindingContext) : Conjunction =
    if (!c.quans.isEmpty)
      c
    else if (isShielded(c, bc))
      Conjunction.FALSE
    else if (c.isNegatedConjunction)
      Conjunction.conj(FilterIt(c.negatedConjs(0).iterator,
                                (d:Conjunction) => !isShieldedNeg(d, bc)),
                       c.order).negate
    else
      // TODO: generalise?
      c

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Only used for runtime assertion purposes
   */
  def freeConstsAreUniversal(bc : BindingContext) : Boolean =
    (constantStatus.keysIterator forall
      (c => (bc binder c) == Some(Quantifier.ALL)))
}
