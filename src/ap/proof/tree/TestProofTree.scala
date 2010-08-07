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
