/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof

import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.proof.goal._
import ap.proof.tree._
import ap.util.{Debug, Seqs, Timeout, OpCounters}
import ap.parameters.{GoalSettings, Param}

/**
 * Prover to eliminate quantifiers in a PA formula. The prover is losely
 * based on the idea in the paper
 *   "A Quantifier Elimination Algorithm for Linear Real Arithmetic"
 * by David Monniaux, although it does not explicitly compute solutions
 * of the matrix of a quantified formula like in the paper. Instead, the
 * constraint extracted from an exhaustive subtree is injected as a lemma
 * into other subtrees and used to close such subtrees earlier.
 * 
 * It is assumed that it is never necessary to adjust the constant freedom of a
 * proof tree in this setting, because all constants that shield formulas also
 * have to be eliminated constants and, thus, never occur in constraints
 * anyway. This makes it possible to construct proof trees in a purely
 * depth-first way (just like in the <code>ModelSearchProver</code>)
 *
 * TODO: at the moment, this prover does not support theories like
 * bit-vectors or multiplication
 */
object QuantifierElimProver {

  private val AC = Debug.AC_PROVER

  private val simplifier = ConstraintSimplifier.NO_SIMPLIFIER
  private val ptf = new SimpleProofTreeFactory(true, simplifier)

  private val basicSettings =
    Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT, simplifier)
  private val completeCNFSettings =
    Param.FULL_SPLITTING.set(basicSettings, true)
  private val nonCompleteCNFSettings =
    Param.FULL_SPLITTING.set(basicSettings, false)
  
  //////////////////////////////////////////////////////////////////////////////
  
  def apply(inputFor : Formula,
            // fully transform the given formula into CNF,
            // instead of leaving subformulae that are not relevant
            // for quantifier elimination unexpanded
            completeCNF : Boolean,
            order : TermOrder) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(QuantifierElimProver.AC,
                    ((Conjunction collectQuantifiers inputFor) subsetOf Set(Quantifier.ALL)) &&
                    (order isSortingOf inputFor))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val settings = if (completeCNF) completeCNFSettings else nonCompleteCNFSettings
    val goal = Goal(List(Conjunction.conj(inputFor, order)), Set(),
                    Vocabulary(order), settings)
    expandProof(goal, Conjunction.FALSE, 0)
  }

  private def checkPruning(goal : Goal) =
    goal.tasks.max match {
      case _ : WrappedFormulaTask => { assert(false); true } // should currently not happen
      case task : BetaFormulaTask => !task.addToQFClauses
      case OmegaTask => OmegaTask.splittingNecessary(goal)
      case EliminateFactsTask => true
      case _ => false
    }

  private def reduceConstraint(c : Conjunction, order : TermOrder) =
    if (c.isTrue || c.isFalse)
      c
    else
      ReduceWithConjunction(Conjunction.TRUE, order)(c)
  
  private def expandProof(tree : ProofTree,
                          // if the following formula can be reduced to true,
                          // proving on this branch can be stopped
                          pruningFor : Conjunction,
                          depth : Int) : Conjunction = {
    Timeout.check
    
    if (!tree.stepPossible) {
//      println("backtracking (depth " + depth + ")")
      OpCounters.inc(OpCounters.Backtrackings3)
      tree.closingConstraint
    } else tree match { 
      case goal : Goal =>
        if (checkPruning(goal)) {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(QuantifierElimProver.AC,
                          // check that no defined symbols occur in the
                          // pruning criterion
                          (goal definedSyms pruningFor) == pruningFor)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          val newPruningFor = goal definedSyms (
                 goal.reduceWithFacts.tentativeReduce(pruningFor))
          if (newPruningFor.isTrue) {
//            println("pruning")
            Conjunction.TRUE
          } else
            expandProof(goal.step(ptf), newPruningFor, depth)
        } else {
          expandProof(goal.step(ptf), pruningFor, depth)            
        }

      case WeakenTree(disjunct, subtree) =>
        reduceConstraint(
          Conjunction.disj(Array(expandProof(subtree, pruningFor, depth), disjunct),
                           tree.order), tree.order)

      case QuantifiedTree(Quantifier.ALL, consts, subtree) => {
        // quantifiers can be ignored, because it is assumed that eliminated
        // constants actually are eliminated and do not occur in constraints
        val res = expandProof(subtree, pruningFor, depth)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(QuantifierElimProver.AC,
                        Seqs.disjointSeq(res.constants, consts))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        res
      }

      case tree : AndTree => {
        OpCounters.inc(OpCounters.Splits3)

        val leftRes =
          expandProof(tree.left, pruningFor, depth + 1)
        val resAndPruningFor =
          Conjunction.disj(Array(pruningFor, leftRes.negate), tree.order)
        val rightRes = expandProof(tree.right, resAndPruningFor, depth + 1)
        reduceConstraint(Conjunction.conj(Array(leftRes, rightRes), tree.order),
                         tree.order)
      }
      
    }
  }
  
}
