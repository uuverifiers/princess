/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.goal.Goal
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object StrengthenTree {

  private val AC = Debug.AC_PROOF_TREE

  def apply(subtree : ProofTree,
            conjunct : Conjunction,
            vocabulary : Vocabulary,
            simplifier : ConstraintSimplifier) : ProofTree =
    if (conjunct.isTrue) {
      subtree
    } else subtree match {

      case subtree : AndTree =>
        AndTree(StrengthenTree(subtree.left, conjunct, vocabulary, simplifier),
                StrengthenTree(subtree.right, conjunct, vocabulary, simplifier),
                vocabulary, subtree.partialCertificate, simplifier)

      case subtree : WeakenTree => {
        val order = vocabulary.order
        val newDisjunct =
          simplifier(Conjunction.conj(Array(subtree.disjunct, conjunct),
                                      order), order)
        WeakenTree(
          StrengthenTree(subtree.subtree, conjunct, vocabulary, simplifier),
          newDisjunct, vocabulary)
      }

      case subtree : StrengthenTree => {
        val order = vocabulary.order
        val newConjunct =
          Conjunction.conj(Array(subtree.conjunct, conjunct), order)
        StrengthenTree(subtree.subtree, newConjunct, vocabulary, simplifier)
      }

      case subtree : ProofTreeOneChild =>
        subtree.update(StrengthenTree(subtree.subtree, conjunct,
                                      subtree.subtree.vocabulary, simplifier),
                       vocabulary.constantFreedom)

      case goal : Goal =>
        new StrengthenTree(goal, conjunct, vocabulary, simplifier)

    }
  
  def unapply(p : ProofTree) : Option[(Conjunction, ProofTree)] = p match {
    case p : StrengthenTree => Some((p.conjunct, p.subtree))
    case _ => None
  }
  
}

/**
 * <code>ProofTreeOneChild</code> that strengthens the closing constraint of its
 * <code>subtree</code> by conjoining a formula
 */
class StrengthenTree private (val subtree : ProofTree,
                              val conjunct : Conjunction,
                              val vocabulary : Vocabulary,
                              simplifier : ConstraintSimplifier)
      extends { protected val subtreeOrder : TermOrder = vocabulary.order }
              with ProofTreeOneChild {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(StrengthenTree.AC,
                   (order isSortingOf conjunct) &&
                   !conjunct.isTrue &&
                   subtree.isInstanceOf[Goal]
)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  lazy val closingConstraint : Conjunction =
    constantFreedom.unshieldedPart(simplifier(
      Conjunction.conj(Array(subtree.closingConstraint, conjunct),
                       order), order), bindingContext)
    
  lazy val closingConstantFreedom : ConstantFreedom =
    subtree.closingConstantFreedom.findNonFreeness(closingConstraint, bindingContext)

  lazy val fixedConstantFreedom : Boolean =
    subtree.fixedConstantFreedom && constantFreedom == closingConstantFreedom 

  lazy val stepMeaningful : Boolean = subtree.stepMeaningful && !conjunct.isFalse

  def update(newSubtree : ProofTree,
             newConstantFreedom : ConstantFreedom) : ProofTree =
    if (subtree == newSubtree && constantFreedom == newConstantFreedom)
      this
    else
      StrengthenTree(newSubtree, conjunct,
                     vocabulary updateConstantFreedom newConstantFreedom,
                     simplifier)
  
  def newConstantFreedomForSubtree(cf : ConstantFreedom) : ConstantFreedom = cf

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String =
    "^ " + closingConstraint + " (/\\ " + conjunct + ")\n" + subtree

}