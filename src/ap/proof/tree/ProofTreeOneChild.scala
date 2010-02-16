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

package ap.proof.tree;

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

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(ProofTreeOneChild.AC,
                   subtreeOrder isSortingOf subtree.closingConstraint)
  //////////////////////////////////////////////////////////////////////////////
   
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
