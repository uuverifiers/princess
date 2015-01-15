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

package ap.proof.tree;

import ap.proof._
import ap.proof.certificates.PartialCertificate
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, Logic}

object AndTree {
  
  private val AC = Debug.AC_PROOF_TREE

  def apply(left : ProofTree, right : ProofTree,
            vocabulary : Vocabulary,
            partialCert : PartialCertificate,
            simplifier : ConstraintSimplifier) : ProofTree = {
    val heightDiff = heightOf(right) - heightOf(left)
    if (heightDiff > 1) {
      // then right is an <code>AndTree</code> that is very deep
      val (rightCert, AndTree(rightLeft, rightRight, _)) = collectCertificates(right)
      val rootCert = combineCertificates(partialCert, null, rightCert)
      if (heightOf(rightLeft) < heightOf(rightRight)) {
        // left-rotate
        AndTree(AndTree(left, rightLeft, vocabulary, null, simplifier),
                rightRight, vocabulary, rootCert, simplifier)
      } else {
        // right-left-rotate
        val AndTree(rightLeftLeft, rightLeftRight, _) = rightLeft
        AndTree(AndTree(left, rightLeftLeft, vocabulary, null, simplifier),
                AndTree(rightLeftRight, rightRight, vocabulary, null, simplifier),
                vocabulary, rootCert, simplifier)
      }
    } else if (heightDiff < -1) {
      // then left is an <code>AndTree</code> that is very deep
      val (leftCert, AndTree(leftLeft, leftRight, _)) = collectCertificates(left)
      val rootCert = combineCertificates(partialCert, leftCert, null)
      if (heightOf(leftRight) < heightOf(leftLeft)) {
        // right-rotate
        AndTree(leftLeft,
                AndTree(leftRight, right, vocabulary, null, simplifier),
                vocabulary, rootCert, simplifier)
      } else {
        // left-right-rotate
        val AndTree(leftRightLeft, leftRightRight, _) = leftRight
        AndTree(AndTree(leftLeft, leftRightLeft, vocabulary, null, simplifier),
                AndTree(leftRightRight, right, vocabulary, null, simplifier),
                vocabulary, rootCert, simplifier)
      }
    } else {
      new AndTree(left, right, vocabulary, partialCert, simplifier)
    }
  }

  def apply(subtrees : Seq[ProofTree], vocabulary : Vocabulary,
            partialCert : PartialCertificate,
            simplifier : ConstraintSimplifier) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, !subtrees.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    subtrees match {
      case Seq(subtree) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, partialCert == null)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        subtree
      }
      case Seq(left, right) =>
        AndTree(left, right, vocabulary, partialCert, simplifier)
      case _ => {
        // divide the subtrees in two parts and recurse
        val mid = (subtrees.size + 1) / 2
        AndTree(AndTree(subtrees.slice(0, mid), vocabulary, null, simplifier),
                AndTree(subtrees.slice(mid, subtrees.size), vocabulary, null, simplifier),
                vocabulary, partialCert, simplifier)
      }
    }
  }
    
  def unapply(t : ProofTree)
             : Option[(ProofTree, ProofTree, PartialCertificate)] = t match {
    case t : AndTree => Some((t.left, t.right, t.partialCertificate))
    case _ => None
  }
  
  private def heightOf(t : ProofTree) : Int = t match {
    case t : AndTree => t.height
    case _ => 0
  }

  /**
   * Number of certificates generated for the given tree. Because partial
   * certificates are only stored for the root of a network of
   * <code>AndTree</code> nodes, it is normal that the inner nodes produce more
   * than one certificate.
   */
  private def certificateArityOf(t : ProofTree) : Int = t match {
    case t : AndTree if (t.partialCertificate == null) =>
      certificateArityOf(t.left) + certificateArityOf(t.right)
    case _ =>
      1
  }
  
  private def combineCertificates(rootCert : PartialCertificate,
                                  leftCert : PartialCertificate,
                                  rightCert : PartialCertificate) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, rootCert != null || leftCert == null && rightCert == null)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (leftCert, rightCert) match {
      case (null, null) =>
        rootCert
      case (leftCert, null) =>
        rootCert compose (List(leftCert) ++
                          Array.fill(rootCert.arity - 1){
                                     PartialCertificate.IDENTITY})
      case (null, rightCert) =>
        rootCert compose (Array.fill(rootCert.arity - 1){
                                     PartialCertificate.IDENTITY} ++
                          List(rightCert))
      case (leftCert, rightCert) =>
        rootCert compose Array(leftCert, rightCert)
    }
  }
  
  private def collectCertificates(t : ProofTree)
                                 : (PartialCertificate, ProofTree) = t match {
    case AndTree(_, _, null) =>
      (null, t)
    case AndTree(left, right, cert) => {
      val (leftCert, newLeft) = collectCertificates(left)
      val (rightCert, newRight) = collectCertificates(right)
      (combineCertificates(cert, leftCert, rightCert),
       t.asInstanceOf[AndTree].update(newLeft, newRight,
                                      null.asInstanceOf[PartialCertificate]))
    }
    case _ =>
      (null, t)
  }
}

class AndTree private (val left : ProofTree, val right : ProofTree,
                       val vocabulary : Vocabulary,
                       val partialCertificate : PartialCertificate,
                       simplifier : ConstraintSimplifier) extends ProofTree {

  import AndTree.{heightOf, certificateArityOf}
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AndTree.AC,
                   // Branching points in proof trees are represented as
                   // balanced binary trees
                   (heightOf(left) - heightOf(right)).abs <= 1 &&
                   // The arities of partial certificates have to be consistent
                   (partialCertificate == null ||
                    partialCertificate.arity ==
                      certificateArityOf(left) + certificateArityOf(right)) &&
                   // partial certificates are always collected at the root
                   (partialCertificate != null ||
                   (left match {
                      case t : AndTree => t.partialCertificate == null
                      case _ => true
                    }) &&
                   (right match {
                      case t : AndTree => t.partialCertificate == null
                      case _ => true
                    })))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  lazy val height : Int = 1 + (heightOf(left) max heightOf(right))

  lazy val subtrees : Seq[ProofTree] = Array(left, right)
    
  lazy val closingConstraint : Conjunction =
    simplifier(Conjunction.conj(for (t <- subtrees.iterator) yield t.closingConstraint,
                                order),
               order)

  lazy val closingConstantFreedom : ConstantFreedom =
    left.closingConstantFreedom meet right.closingConstantFreedom

  lazy val fixedConstantFreedom : Boolean =
    left.fixedConstantFreedom &&
    right.fixedConstantFreedom &&
    constantFreedom == closingConstantFreedom 

  lazy val stepPossible : Boolean =
    Logic.exists(for (subtree <- subtrees.iterator) yield subtree.stepPossible)

  lazy val stepMeaningful : Boolean =
    (left.stepMeaningful, right.stepMeaningful) match {
    case (true, true) => true
    case (true, false) => !right.closingConstraint.isFalse
    case (false, true) => !left.closingConstraint.isFalse
    case (false, false) => false
    }

  def update(newSubtrees : Seq[ProofTree]) : ProofTree =
    AndTree(newSubtrees, vocabulary, partialCertificate, simplifier)

  def update(newLeft : ProofTree, newRight : ProofTree,
             newConstantFreedom : ConstantFreedom) : ProofTree =
    if (left == newLeft && right == newRight &&
        constantFreedom == newConstantFreedom)
      this
    else
      AndTree(newLeft, newRight,
              vocabulary updateConstantFreedom newConstantFreedom,
              partialCertificate,
              simplifier)
    
  def update(newLeft : ProofTree, newRight : ProofTree,
             newPartialCertificate : PartialCertificate) : ProofTree =
    if (left == newLeft && right == newRight &&
        (partialCertificate eq newPartialCertificate))
      this
    else
      AndTree(newLeft, newRight,
              vocabulary, newPartialCertificate,
              simplifier)
    
  /**
   * Given a new constant freedom for this proof tree, derive the corresponding
   * freedoms for the direct subtrees.
   */
  def newConstantFreedomForSubtrees(cf : ConstantFreedom) = (cf, cf)

  //////////////////////////////////////////////////////////////////////////////

  private def indent(str : String, prefix : String) =
    prefix + str.replaceAll("\n", "\n" + prefix)
    
  override def toString : String =
    "^ " + unifiabilityString /* closingConstraint */ + " (/\\)\n" +
      (for (t <- subtrees) yield indent("" + t, "  ")).mkString("\n/\\\n")

}
