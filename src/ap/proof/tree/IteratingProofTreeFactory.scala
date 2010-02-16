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
