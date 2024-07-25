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
import ap.proof.goal.Goal
import ap.terfor.linearcombination.LinearCombination
import ap.terfor._
import ap.util.{Debug, Logic, PlainRange, FilterIt, Seqs}

object TestProofTree {

  private val AC = Debug.AC_PROOF_TREE

  def assertNormalisedTree(t : ProofTree) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, isNormalisedTree(t) &&
                        correctBindings(t, BindingContext.EMPTY) &&
                        t.fixedConstantFreedom)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  }

  /**
   * The information about bound constants is consistent with the actual
   * nodes in the proof tree
   */
  private def correctBindings(t : ProofTree, bc : BindingContext) : Boolean =
    (t match {
       case t : Goal => t.facts.isFalse || t.bindingContext == bc
       case _ => t.bindingContext == bc
    }) &&
    (t match {
       case QuantifiedTree(q, consts, subtree) =>
         correctBindings(subtree, bc.addAndContract(consts, q))
       case t : ProofTreeOneChild =>
         correctBindings(t.subtree, bc)
       case t : AndTree =>
         Logic.forall(for (subtree <- t.subtrees.iterator)
                      yield correctBindings(subtree, bc))
       case _ => true
     })
  
  /**
   * The proof is fully expanded
   */
  private def isNormalisedTree(t : ProofTree) : Boolean =
    // if the closing constraint is true, there is no point in further expanding
    // a proof tree ... so that we cannot rely on the prover doing it
    t.closingConstraint.isTrue ||
    (t match {
    case t : WeakenTree => isNormalisedTree(t.subtree)
    case t : ProofTreeOneChild => isNormalisedTree(t.subtree)
    case t : AndTree => {
      val normalisedSubTrees =
        for (subtree <- t.subtrees) yield isNormalisedTree(subtree)

      !(normalisedSubTrees contains false) ||
      ((normalisedSubTrees.iterator zip t.subtrees.iterator) exists {
         case (norm, tree) => norm && tree.closingConstraint.isFalse
       })
    }
    case goal : Goal =>
      goal.tasks.isEmpty &&
      (goal.facts.isFalse ||
        Logic.forall(for (lc <- goal.facts.arithConj.positiveEqs.iterator)
                     yield isNormalisedPosEq(lc, goal)) &&
        Logic.forall(for (lc <- goal.facts.arithConj.negativeEqs.iterator)
                     yield isNormalisedNegEq(lc, goal)) &&
        goal.facts.arithConj.inEqs.equalityInfs.isTrue &&
        Seqs.disjoint(goal.facts.arithConj.inEqs.constants,
                      goal.eliminatedConstants))
  })
  
  private def isNormalisedPosEq(lc : LinearCombination, goal : Goal) =
    lc.leadingCoeff.isOne
/*    if (goal eliminates lc.leadingTerm)
      (lc.leadingCoeff.isOne ||
       Logic.forall(1, lc.size, (i) => !(goal eliminates (lc(i) _2))))
    else
      lc.leadingCoeff.isOne */

  private def isNormalisedNegEq(lc : LinearCombination, goal : Goal) =
    Logic.forall(for (posLc <- goal.facts.arithConj.positiveEqs.iterator)
                 yield ((lc.leadingTerm != posLc.leadingTerm) &&
                        (if (goal eliminates posLc.leadingTerm)
                           lc.get(posLc.leadingTerm) isAbsMinMod posLc.leadingCoeff
                         else
                           doesNotContain(lc, posLc.leadingTerm))))

  private def doesNotContain(tf : TerFor, t : Term) : Boolean = t match {
    case t : ConstantTerm => !(tf.constants contains t)
    case t : VariableTerm => !(tf.variables contains t)
    case _ => true
  }

}
