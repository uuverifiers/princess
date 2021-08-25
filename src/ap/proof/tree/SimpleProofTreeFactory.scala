/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.certificates.{BranchInferenceCollection, PartialCertificate}
import ap.terfor.{Formula, ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier}
import ap.terfor.arithconj.ModelElement
import ap.terfor.substitutions.Substitution
import ap.parameters.GoalSettings

import scala.collection.mutable.ArrayBuffer

class SimpleProofTreeFactory(removeTask : Boolean,
                             simplifier : ConstraintSimplifier,
                             randomDataSource : RandomDataSource =
                               NonRandomDataSource)
      extends ProofTreeFactory {

  def and(subtrees : Seq[ProofTree],
          partialCertificate : PartialCertificate,
          vocabulary : Vocabulary) : ProofTree =
    if (randomDataSource.isRandom) {
//    println("shuffling ...")
      partialCertificate match {
        case null => {
          val trees = subtrees.toBuffer
          randomDataSource shuffle trees
          AndTree(trees, vocabulary, null, simplifier)
        }
        case pcert => {
          val (newPCert, perm) = pcert shuffle randomDataSource
          val trees = for (i <- perm) yield subtrees(i)
          AndTree(trees, vocabulary, newPCert, simplifier)
        }
      }
    } else {
      AndTree(subtrees, vocabulary, partialCertificate, simplifier)
    }
  
  def andInOrder(subtrees : Seq[ProofTree],
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
               
  def strengthen(subtree : ProofTree,
                 conjunct : Conjunction,
                 vocabulary : Vocabulary) : ProofTree =
    StrengthenTree(subtree, conjunct, vocabulary, simplifier)

  // not supposed to do anything when constructing proofs
  def eliminatedConstant(subtree : ProofTree,
                         m : ModelElement,
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
