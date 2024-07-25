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
import ap.proof.goal.{PrioritisedTask, Goal, TaskManager, CompoundFormulas}
import ap.proof.certificates.BranchInferenceCollection
import ap.terfor.{Formula, ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}
import ap.terfor.substitutions.Substitution
import ap.parameters.GoalSettings

/**
 * Proof tree factory in which updating a goal will recursive apply further
 * rules, until some stopping condition holds
 */
class IteratingProofTreeFactory(stoppingCond : (Goal) => Boolean,
                                simplifier : ConstraintSimplifier)
      extends SimpleProofTreeFactory(true, simplifier) {

  protected override def createNewGoal(updatedFacts : Conjunction,
                                       updatedCompoundFormulas : CompoundFormulas,
                                       updatedElimConstants : Set[ConstantTerm],
                                       updatedVocabulary : Vocabulary,
                                       updatedDefinedSyms : Substitution,
                                       newTasks : TaskManager,
                                       age : Int,
                                       branchInferences : BranchInferenceCollection,
                                       settings : GoalSettings) : ProofTree = {
    val newGoal = Goal(updatedFacts, updatedCompoundFormulas, newTasks, age,
                       updatedElimConstants,
                       updatedVocabulary, updatedDefinedSyms,
                       branchInferences, settings)
    if (!newGoal.stepPossible || stoppingCond(newGoal))
      newGoal
    else
      newGoal step this
  }
  
}
