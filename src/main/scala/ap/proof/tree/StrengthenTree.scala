/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2015 Philipp Ruemmer <ph_r@gmx.net>
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
                   subtree.isInstanceOf[Goal])
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  lazy val closingConstraint : Conjunction = {
    val res = constantFreedom.unshieldedPart(simplifier(
                Conjunction.conj(Array(subtree.closingConstraint, conjunct),
                                 order), order), bindingContext)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(StrengthenTree.AC, order isSortingOf res)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }
    
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
