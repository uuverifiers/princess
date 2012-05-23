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

import ap.CmdlMain
import ap.terfor.TerForConvenience
import ap.proof._
import ap.proof.goal.Goal
import ap.terfor.{TermOrder, ConstantTerm, VariableTerm, Formula}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.parameters.Param
import ap.util.{PlainRange, Debug, Seqs}

object QuantifiedTree {
  
  private val AC = Debug.AC_PROOF_TREE
  
  def apply(subtree : ProofTree,
            quan : Quantifier,
            quantifiedConstants : Seq[ConstantTerm],
            guard : Conjunction,
            vocabulary : Vocabulary,
            subtreeOrder : TermOrder,
            simplifier : ConstraintSimplifier) : ProofTree = subtree match {
    case subtree : QuantifiedTree if (subtree.quan == quan) =>
      QuantifiedTree(subtree.subtree,
                     quan,
                     quantifiedConstants ++ subtree.quantifiedConstants,
                     Conjunction.conj(Array(guard, subtree.guard), subtree.subtreeOrder),
                     vocabulary, subtree.subtreeOrder,
                     simplifier)
    case subtree : AndTree if (quan == Quantifier.ALL) =>
      AndTree(for (t <- subtree.subtrees)
              yield QuantifiedTree(t, quan, quantifiedConstants, Conjunction.TRUE,
                                   vocabulary, subtreeOrder, simplifier),
              vocabulary, subtree.partialCertificate, simplifier)
    case subtree : WeakenTree if (quan == Quantifier.EX) =>
      WeakenTree(QuantifiedTree(subtree.subtree,
                                quan, quantifiedConstants, guard,
                                vocabulary, subtreeOrder, simplifier),
                 quantifySimplify(subtree.disjunct, quan, quantifiedConstants,
                                  guard,
                                  vocabulary.order, subtreeOrder, simplifier,
                                  vocabulary.bindingContext, subtree),
                 vocabulary)
    case subtree : WeakenTree if (Seqs.disjointSeq(subtree.disjunct.constants,
                                                   quantifiedConstants)) =>
      WeakenTree(QuantifiedTree(subtree.subtree,
                                quan, quantifiedConstants, guard,
                                vocabulary, subtreeOrder, simplifier),
                 vocabulary.order sort subtree.disjunct,
                 vocabulary)
    case _ => 
      new QuantifiedTree(subtree, quan, quantifiedConstants, guard,
                         vocabulary, subtreeOrder,
                         simplifier)
  }
 
  def unapply(tree : ProofTree) : Option[(Quantifier, Seq[ConstantTerm], ProofTree)] =
    tree match {
      case tree : QuantifiedTree => Some(tree.quan, tree.quantifiedConstants, tree.subtree)
      case _ => None
    }
  
  private def quantify(f : Conjunction,
                       quan : Quantifier, quantifiedConstants : Seq[ConstantTerm],
                       guard : Conjunction,
                       outputOrder : TermOrder, inputOrder : TermOrder,
                       context : BindingContext,
                       subtree : ProofTree) : Conjunction = quan match {
    case Quantifier.EX => {
      import TerForConvenience._
      implicit val o = inputOrder
    
      val domainConstraint = addFiniteDomainConstraints(subtree) match {
        case Param.FiniteDomainConstraints.DomainSize =>
          conj(for (c <- quantifiedConstants.iterator)
               yield (c >= 0 & c < CmdlMain.domain_size))
        case Param.FiniteDomainConstraints.VocabularyEquations =>
          conj(for (c <- quantifiedConstants.iterator)
               yield disjFor(for (d <- context.universallyBoundConstants)
                             yield (c === d)))
        case Param.FiniteDomainConstraints.None |
             Param.FiniteDomainConstraints.TypeGuards =>
          Conjunction.TRUE
      }
    
      Conjunction.quantify(quan, quantifiedConstants,
                           Conjunction.conj(Array(domainConstraint, f, guard),
                                            inputOrder),
                           inputOrder) sortBy outputOrder
    }
    
    case Quantifier.ALL =>
      Conjunction.quantify(quan, quantifiedConstants, f, inputOrder) sortBy outputOrder
  }
  
  private def quantifySimplify(f : Conjunction,
                               quan : Quantifier, quantifiedConstants : Seq[ConstantTerm],
                               guard : Conjunction,
                               outputOrder : TermOrder, inputOrder : TermOrder,
                               simplifier : ConstraintSimplifier,
                       context : BindingContext,
                               subtree : ProofTree) : Conjunction =  
    simplifier(quantify(f, quan, quantifiedConstants, guard,
                        outputOrder, inputOrder, context, subtree),
               outputOrder)
  
  private def addFiniteDomainConstraints(tree : ProofTree)
              : Param.FiniteDomainConstraints.Value = tree match {
    case goal : Goal => Param.FINITE_DOMAIN_CONSTRAINTS(goal.settings)
    case tree => addFiniteDomainConstraints(tree.subtrees.head)
  }
                    
}

/**
 * <code>ProofTreeOneChild</code> that quantifies a set of constants in
 * the closing constraint of its <code>subtree</code>
 */
class QuantifiedTree private (val subtree : ProofTree,
                              val quan : Quantifier,
                              val quantifiedConstants : Seq[ConstantTerm],
                              val guard : Conjunction,
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
                    }) &&
                    (this.quan != Quantifier.ALL || guard.isTrue) &&
                    (guard isSortedBy subtreeOrder))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  lazy val closingConstraint : Conjunction =
    simplifier(QuantifiedTree.quantify(subtree.closingConstraint,
                                       quan,
                                       quantifiedConstants, guard,
                                       order, subtreeOrder,
                                       vocabulary.bindingContext, subtree), order)
  
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
      QuantifiedTree(newSubtree, quan, quantifiedConstants, guard,
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
