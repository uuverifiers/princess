/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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
                   !disjunct.isFalse &&
                   !subtree.isInstanceOf[WeakenTree])
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private lazy val unshieldedDisjunct =
    constantFreedom.unshieldedPart(disjunct, bindingContext) 
  
  lazy val closingConstraint : Conjunction =
    Conjunction.disj(Array(subtree.closingConstraint, unshieldedDisjunct),
                     order)
    
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
