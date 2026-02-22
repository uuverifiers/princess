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

package ap.proof.tree;

import ap.proof._
import ap.terfor.TermOrder
import ap.util.Debug

object ProofTreeOneChild {
  
  private val AC = Debug.AC_PROOF_TREE
  
  def unapply(p : ProofTree) : Option[ProofTree] = p match {
    case p : ProofTreeOneChild => Some(p.subtree)
    case _ => None
  }
  
}

/**
 * Common superclass for proof trees that have exactly one direct subtree. Such
 * trees know about two <code>TermOrder</code>s: the <code>TermOrder</code> of
 * the closing constraint coming from the subtree, and the
 * <code>TermOrder</code> of the constraint of this <code>ProofTree</code>
 */
trait ProofTreeOneChild extends ProofTree {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ProofTreeOneChild.AC,
                   subtreeOrder isSortingOf subtree.closingConstraint)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
   
  val subtree : ProofTree

  lazy val subtrees : Seq[ProofTree] = List(subtree)

  lazy val stepPossible : Boolean = subtree.stepPossible

  /**
   * Replace the subtree and the constant freedom status with new values.
   */
  def update(newSubtree : ProofTree,
             newConstantFreedom : ConstantFreedom) : ProofTree
  
  /**
   * Given a new constant freedom for this proof tree, derive the corresponding
   * freedom for the direct subtree.
   */
  def newConstantFreedomForSubtree(cf : ConstantFreedom) : ConstantFreedom
  
  protected val subtreeOrder : TermOrder
  
}
