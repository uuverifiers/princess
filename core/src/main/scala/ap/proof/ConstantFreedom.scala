/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof

import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0,
                                    LinearCombination1}
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

  def isBottomWRT(constant : ConstantTerm) : Boolean =
    constantStatus(constant) == NonFree

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

  /**
   * Give the given constants bottom status.
   */
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
    (c.negatedConjs exists (isAllShieldedNeg(_, bc)))
  
  /**
   * Determine whether the formula <code>lc1 - lc2 = 0 & phi</code> is shielded
   * (for arbitrary <code>phi</code>)
   */
  def diffIsShieldingLC(lc1 : LinearCombination, lc2 : LinearCombination,
                        bc : BindingContext) : Boolean = {
    (lc1, lc2) match {
      case (lc1 : LinearCombination0, lc2 : LinearCombination0) =>
        lc1.constant != lc2.constant
      case (lc1 : LinearCombination0, lc2 : LinearCombination1) =>
        lc2.term0 match {
          case c : ConstantTerm =>
            constantStatus(c) != NonFree
          case _ =>
            false
        }
      case (lc1 : LinearCombination1, lc2 : LinearCombination0) =>
        lc1.term0 match {
          case c : ConstantTerm =>
            constantStatus(c) != NonFree
          case _ =>
            false
        }
      case (lc1 : LinearCombination1, lc2 : LinearCombination1) =>
        (lc1.term0, lc2.term0) match {
          case (c : ConstantTerm, d : ConstantTerm) =>
            if (c == d) {
              if (lc1.coeff0 == lc2.coeff0)
                lc1.constant != lc2.constant
              else
                constantStatus(c) != NonFree
            } else {
              (bc.lteq(c, d) && constantStatus(d) != NonFree) ||
              (bc.lteq(d, c) && constantStatus(c) != NonFree)
            }
          case _ =>
            false
        }
      case _ =>
        lc1.variables.isEmpty && lc2.variables.isEmpty && {
          val remainingConsts =
            (lc1.constants ++ lc2.constants) filter (
              (c) => (lc1 get c) != (lc2 get c))
          if (remainingConsts.isEmpty)
            lc1.constant != lc2.constant
          else
            bc.containsMaximumConstantWith(
              remainingConsts, (constantStatus(_) != NonFree))
        }
    }
  }
  
  private def isShieldingLC(lc : LinearCombination, bc : BindingContext) : Boolean =
    lc.variables.isEmpty &&
    bc.containsMaximumConstantWith(lc.constants, (constantStatus(_) != NonFree))

  /**
   * Check whether <code>c</code>, seen as a negated conjunction,
   * only consists of shielded terms. E.g., <code>!(A & B) = !A | !B</code>,
   * where both <code>!A</code> and <code>!B</code> are shielded
   */
  private def isAllShieldedNeg(c : Conjunction, bc : BindingContext) : Boolean =
    c.arithConj.positiveEqs.isTrue &&
    c.arithConj.inEqs.isTrue &&
    c.predConj.isTrue &&
    (c.arithConj.negativeEqs forall (isShieldingLC(_, bc))) &&
    (c.negatedConjs forall (isShielded(_, bc)))
    
  /**
   * Determine the (disjunctively connected) unshielded part of a formula
   */
  def unshieldedPart(c : Conjunction, bc : BindingContext) : Conjunction =
    if (!c.quans.isEmpty)
      c
    else if (isShielded(c, bc))
      Conjunction.FALSE
    else if (c.isNegatedConjunction) {
      implicit val order = c.order
      
      val negConj = c.negatedConjs(0)
      
      val arithConj = negConj.arithConj
      val newNegativeEqs =
        arithConj.negativeEqs.updateEqsSubset(
          arithConj.negativeEqs filterNot (isShieldingLC(_, bc)))
      val newArithConj = arithConj updateNegativeEqs newNegativeEqs

      val newNegatedConjs =
        negConj.negatedConjs.updateSubset(
          negConj.negatedConjs filterNot (isShielded(_, bc)), order)
      
      Conjunction(List(), newArithConj, negConj.predConj, newNegatedConjs,
                  order).negate
    } else
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
