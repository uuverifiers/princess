/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.{TermOrder, ConstantTerm, VariableTerm, Formula}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.util.{PlainRange, Debug, Seqs}

object QuantifiedTree {
  
  private val AC = Debug.AC_PROOF_TREE
  
  def apply(subtree : ProofTree,
            quan : Quantifier,
            quantifiedConstants : Seq[ConstantTerm],
            vocabulary : Vocabulary,
            subtreeOrder : TermOrder,
            simplifier : ConstraintSimplifier) : ProofTree = subtree match {
    case subtree : QuantifiedTree if (subtree.quan == quan) =>
      QuantifiedTree(subtree.subtree,
                     quan,
                     quantifiedConstants ++ subtree.quantifiedConstants,
                     vocabulary, subtree.subtreeOrder,
                     simplifier)
    case subtree : AndTree if (quan == Quantifier.ALL) =>
      AndTree(for (t <- subtree.subtrees)
              yield QuantifiedTree(t, quan, quantifiedConstants, vocabulary,
                                   subtreeOrder, simplifier),
              vocabulary, subtree.partialCertificate, simplifier)
    case subtree : WeakenTree if (quan == Quantifier.EX) =>
      WeakenTree(QuantifiedTree(subtree.subtree,
                                quan, quantifiedConstants,
                                vocabulary, subtreeOrder, simplifier),
                 quantifySimplify(subtree.disjunct, quan, quantifiedConstants,
                                  vocabulary.order, subtreeOrder, simplifier),
                 vocabulary)
    case subtree : WeakenTree if (Seqs.disjointSeq(subtree.disjunct.constants,
                                                   quantifiedConstants)) =>
      WeakenTree(QuantifiedTree(subtree.subtree,
                                quan, quantifiedConstants,
                                vocabulary, subtreeOrder, simplifier),
                 vocabulary.order sort subtree.disjunct,
                 vocabulary)
    case _ => 
      new QuantifiedTree(subtree, quan, quantifiedConstants, vocabulary, subtreeOrder,
                         simplifier)
  }
 
  def unapply(tree : ProofTree) : Option[(Quantifier, Seq[ConstantTerm], ProofTree)] =
    tree match {
      case tree : QuantifiedTree => Some(tree.quan, tree.quantifiedConstants, tree.subtree)
      case _ => None
    }
  
  private def quantify(f : Conjunction,
                       quan : Quantifier, quantifiedConstants : Seq[ConstantTerm],
                       outputOrder : TermOrder, inputOrder : TermOrder) : Conjunction =
    Conjunction.quantify(quan, quantifiedConstants,
                         f, inputOrder) sortBy outputOrder
  
  private def quantifySimplify(f : Conjunction,
                               quan : Quantifier, quantifiedConstants : Seq[ConstantTerm],
                               outputOrder : TermOrder, inputOrder : TermOrder,
                               simplifier : ConstraintSimplifier) : Conjunction =  
    simplifier(quantify(f, quan, quantifiedConstants, outputOrder, inputOrder),
               outputOrder)
  
}

/**
 * <code>ProofTreeOneChild</code> that quantifies a set of constants in
 * the closing constraint of its <code>subtree</code>
 */
class QuantifiedTree private (val subtree : ProofTree,
                              val quan : Quantifier,
                              val quantifiedConstants : Seq[ConstantTerm],
                              val vocabulary : Vocabulary,
                              protected val subtreeOrder : TermOrder,
                              simplifier : ConstraintSimplifier)
      extends ProofTreeOneChild {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(QuantifiedTree.AC,
                   !quantifiedConstants.isEmpty &&
                   (subtree match {
                     case subtree : QuantifiedTree => subtree.quan != this.quan
                     case subtree : AndTree => this.quan != Quantifier.ALL
                     case subtree : WeakenTree if (this.quan == Quantifier.EX) =>
                       false
                     case subtree : WeakenTree if (this.quan == Quantifier.ALL) =>
                       !Seqs.disjointSeq(subtree.disjunct.constants, quantifiedConstants)
                     case _ => true
                    }))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  lazy val closingConstraint : Conjunction = {
    val res =
      simplifier(QuantifiedTree.quantify(subtree.closingConstraint, quan,
                                         quantifiedConstants,
                                         order, subtreeOrder),
                 order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(QuantifiedTree.AC, order isSortingOf res)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }
  
  lazy val closingConstantFreedom : ConstantFreedom =
    if (quan == Quantifier.ALL)
      subtree.closingConstantFreedom -- quantifiedConstants
    else {
/*      val res = subtree.closingConstantFreedom
      if (res < constantFreedom) {
        val u = constantFreedom.unshieldedPart(closingConstraint, bindingContext)
        val c = constantFreedom.findNonFreeness(u, bindingContext)
        if (res < c)
        println("hallo")
      }
      res */
      subtree.closingConstantFreedom
    }

  lazy val fixedConstantFreedom : Boolean =
    subtree.fixedConstantFreedom && constantFreedom == closingConstantFreedom 

  lazy val stepMeaningful : Boolean = subtree.stepMeaningful

  def update(newSubtree : ProofTree,
             newConstantFreedom : ConstantFreedom) : ProofTree =
    if (subtree == newSubtree && constantFreedom == newConstantFreedom)
      this
    else
      QuantifiedTree(newSubtree, quan, quantifiedConstants,
                     vocabulary updateConstantFreedom newConstantFreedom,
                     subtreeOrder, simplifier)

  def newConstantFreedomForSubtree(cf : ConstantFreedom) : ConstantFreedom =
    if (quan == Quantifier.ALL)
      (cf addTopStatus quantifiedConstants) meet subtree.closingConstantFreedom
    else
      cf

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String =
    "^ " + closingConstraint + " (" +
    quan + " " +
    (for (c <- quantifiedConstants) yield c.toString).mkString(" ") +
    ")\n" + subtree

}
