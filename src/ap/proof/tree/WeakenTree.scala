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

package ap.proof.tree;

import ap.proof._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object WeakenTree {
  
  private val AC = Debug.AC_PROOF_TREE

  def apply(subtree : ProofTree,
            disjunct : Conjunction,
            vocabulary : Vocabulary) : ProofTree =
    if (disjunct.isFalse) {
      subtree
    } else subtree match {
      case subtree : WeakenTree =>
        WeakenTree(subtree.subtree,
                   Conjunction.disj(Array(subtree.disjunct, disjunct),
                                    vocabulary.order),
                   vocabulary)
      case _ => new WeakenTree(subtree, disjunct, vocabulary)
    }
  
  def unapply(p : ProofTree) : Option[(Conjunction, ProofTree)] = p match {
    case p : WeakenTree => Some((p.disjunct, p.subtree))
    case _ => None
  }
  
}

/**
 * <code>ProofTreeOneChild</code> that weakens the closing constraint of its
 * <code>subtree</code> by disjunctively adding a formula
 */
class WeakenTree private (val subtree : ProofTree,
                          val disjunct : Conjunction,
                          val vocabulary : Vocabulary)
      extends { protected val subtreeOrder : TermOrder = vocabulary.order }
              with ProofTreeOneChild {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(WeakenTree.AC,
                   (order isSortingOf disjunct) &&
                   !subtree.isInstanceOf[WeakenTree])
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private lazy val unshieldedDisjunct =
    constantFreedom.unshieldedPart(disjunct, bindingContext) 
  
  lazy val closingConstraint : Conjunction =
    Conjunction.disj(Array(subtree.closingConstraint, unshieldedDisjunct),
                     subtreeOrder)
    
  lazy val closingConstantFreedom : ConstantFreedom =
    subtree.closingConstantFreedom.findNonFreeness(unshieldedDisjunct, bindingContext)

  lazy val fixedConstantFreedom : Boolean =
    subtree.fixedConstantFreedom && constantFreedom == closingConstantFreedom 

  lazy val stepMeaningful : Boolean = subtree.stepMeaningful && !disjunct.isTrue

  def update(newSubtree : ProofTree,
             newConstantFreedom : ConstantFreedom) : ProofTree =
    if (subtree == newSubtree && constantFreedom == newConstantFreedom)
      this
    else
      WeakenTree(newSubtree, disjunct,
                 vocabulary updateConstantFreedom newConstantFreedom)
  
  def newConstantFreedomForSubtree(cf : ConstantFreedom) : ConstantFreedom = cf

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String =
    "^ " + closingConstraint + " (\\/ " + disjunct + ")\n" + subtree

}
