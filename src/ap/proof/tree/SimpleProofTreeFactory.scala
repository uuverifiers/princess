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

import ap.proof._
import ap.proof.goal.{PrioritisedTask, Goal, TaskManager, CompoundFormulas}
import ap.proof.certificates.{BranchInferenceCollection, PartialCertificate}
import ap.terfor.{Formula, ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier}
import ap.terfor.substitutions.Substitution
import ap.parameters.GoalSettings

class SimpleProofTreeFactory(removeTask : Boolean,
                             simplifier : ConstraintSimplifier) extends ProofTreeFactory {

  def and(subtrees : Seq[ProofTree],
          partialCertificate : PartialCertificate,
          vocabulary : Vocabulary) : ProofTree =
    AndTree(subtrees, vocabulary, partialCertificate, simplifier)
  
  def quantify(subtree : ProofTree,
               quan : Quantifier,
               quantifiedConstants : Seq[ConstantTerm],
               vocabulary : Vocabulary,
               subtreeOrder : TermOrder) : ProofTree =
    QuantifiedTree(subtree, quan, quantifiedConstants,
                   vocabulary, subtreeOrder, simplifier)
  
  def weaken(subtree : ProofTree,
             disjunct : Conjunction,
             vocabulary : Vocabulary) : ProofTree =
    WeakenTree(subtree, disjunct, vocabulary)
               
  // not supposed to do anything when constructing proofs
  def eliminatedConstant(subtree : ProofTree,
                         cs : Seq[ConstantTerm],
                         witness : (Substitution, TermOrder) => Substitution,
                         vocabulary : Vocabulary) : ProofTree =
     subtree
    
  //////////////////////////////////////////////////////////////////////////////
  
  protected def createNewGoal(updatedFacts : Conjunction,
                              updatedCompoundFormulas : CompoundFormulas,
                              updatedElimConstants : Set[ConstantTerm],
                              updatedVocabulary : Vocabulary,
                              updatedDefinedSyms : Substitution,
                              newTasks : TaskManager,
                              age : Int,
                              branchInferences : BranchInferenceCollection,
                              settings : GoalSettings) : ProofTree =
    Goal(updatedFacts, updatedCompoundFormulas, newTasks, age,
         updatedElimConstants, updatedVocabulary, updatedDefinedSyms,
         branchInferences, settings)
    
  def updateGoal(updatedFacts : Conjunction,
                 updatedCompoundFormulas : CompoundFormulas,
                 updatedElimConstants : Set[ConstantTerm],
                 updatedVocabulary : Vocabulary,
                 updatedDefinedSyms : Substitution,
                 newTasks : Iterable[PrioritisedTask],
                 updatedInferences : BranchInferenceCollection,
                 goal : Goal) : ProofTree = {
    val updatedTasks = (if (removeTask)
                          goal.tasks.removeFirst
                        else
                          goal.tasks) ++ newTasks
    createNewGoal(updatedFacts, updatedCompoundFormulas, updatedElimConstants,
                  updatedVocabulary, updatedDefinedSyms,
                  updatedTasks, goal.age + 1, updatedInferences, goal.settings)
  }

  def updateGoal(updatedFacts : Conjunction,
                 updatedCompoundFormulas : CompoundFormulas,
                 updatedElimConstants : Set[ConstantTerm],
                 updatedVocabulary : Vocabulary,
                 updatedDefinedSyms : Substitution,
                 updatedTaskManager : TaskManager,
                 updatedInferences : BranchInferenceCollection,
                 goal : Goal) : ProofTree =
    createNewGoal(updatedFacts, updatedCompoundFormulas, updatedElimConstants,
                  updatedVocabulary, updatedDefinedSyms,
                  updatedTaskManager, goal.age + 1, updatedInferences,
                  goal.settings)

}
