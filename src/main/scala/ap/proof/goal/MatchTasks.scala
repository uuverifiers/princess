/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.proof.Vocabulary
import ap.proof.certificates.BranchInferenceCollector
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.theoryPlugins.IntermediatePluginTask
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier,
                               IterativeClauseMatcher}
import ap.terfor.{ConstantTerm, VariableTerm, TermOrder}
import ap.parameters.Param
import ap.util.Debug

import scala.collection.mutable.ArrayBuffer

object MatchTasks {

  /**
   * Add the prioritised tasks for handling predicates: the
   * <code>LazyMatchtask</code> and
   * <code>IntermediatePluginTask</code>.
   */
  def addPredicateTasks(goal : Goal) : Seq[PrioritisedTask] = {
    val tasks1 = LazyMatchTask addTask goal
    val tasks2 = IntermediatePluginTask addTask goal
    tasks1 ++ tasks2
  }

}

private object MatchFunctions {
  
  def isIrrelevantInstance(instance : Conjunction,
                           voc : Vocabulary,
                           // the constants occurring in all formulae that were
                           // used to generate this instance; this might be
                           // fewer/different constants than occurring in the
                           // (reduced) instance, due to rewriting
                           originatingConstants : scala.collection.Set[ConstantTerm],
                           reversePropagation : Boolean) =
    reversePropagation && 
    !(AddFactsTask isCoveredFormula instance) && {
      val constantFreedom =
        if (instance.constants subsetOf originatingConstants)
          voc.constantFreedom
        else
          // we assume the worst (non-free status) for constants that occur
          // in the reduced instance, but do not occur in any of the formulae
          // from which the instance was derived. otherwise, we might rule
          // out too many instances as irrelevant, but not reconsider them
          // at a later point
          voc.constantFreedom -- (instance.constants -- originatingConstants)
      constantFreedom.isShielded(instance, voc.bindingContext)
    }
  
  def updateMatcher(goal : Goal,
                    ptf : ProofTreeFactory,
                    eager : Boolean) : ProofTree = {
    val collector  = goal.getInferenceCollector
    val oldMatcher = goal.compoundFormulas quantifierClauses eager

    // first check whether any of the clauses has to be updated
    val (reducedMatcher, removedClauseTasks) =
      reduceMatcherClauses(goal, oldMatcher, collector)

    // then match using new facts available in the goal
    val (newMatcher, instanceTasks) =
      updateMatcherFacts(goal, reducedMatcher, collector)

    val allTasks =
      removedClauseTasks ++ instanceTasks

    val newCF =
      goal.compoundFormulas.updateQuantifierClauses(eager, newMatcher)
    ptf.updateGoal(newCF, allTasks, collector.getCollection, goal)
  }

  private def updateMatcherFacts(goal : Goal,
                                 matcher : IterativeClauseMatcher,
                                 collector : BranchInferenceCollector)
                              : (IterativeClauseMatcher,
                                 Iterable[PrioritisedTask]) = {
    val order = goal.order
    val voc = goal.vocabulary
  
    val reverseProp = Param.REVERSE_FUNCTIONALITY_PROPAGATION(goal.settings)
    val (instances, newMatcher) =
      matcher.updateFacts(goal.facts.predConj,
                          goal.mayAlias,
                          goal.reduceWithFacts,
                          isIrrelevantInstance(_, voc, _, reverseProp),
                          reverseProp,
                          collector, order)

    // check whether some of the instances are useless and blocked
    // for the time being
    val blockedTasks = new ArrayBuffer[BlockedFormulaTask]

    val normalInstances =
      for (f <- instances;
           if (BlockedFormulaTask.isBlocked(f, goal) match {
                 case Some(t) => { blockedTasks += t; false }
                 case None => true
               }))
      yield f

    val newTasks =
      if (collector.isLogging)
        // if we are producing proofs, we have to treat the instances
        // separately (to log all performed simplifications)
        for (f <- normalInstances; t <- goal.formulaTasks(f)) yield t
      else
        for (t <- goal.formulaTasks(
               goal reduceWithFacts disjPullOutAll(normalInstances, order)))
        yield t

    (newMatcher, newTasks ++ blockedTasks)
  }

  private def reduceMatcherClauses(goal : Goal,
                                   matcher : IterativeClauseMatcher,
                                   collector : BranchInferenceCollector)
                                : (IterativeClauseMatcher,
                                   Iterable[PrioritisedTask]) = {
    val order = goal.order

    val (removedClauses, reducedMatcher) =
      if (collector.isLogging) {
        // if we are producing proofs, we mostly check for subsumed clauses
        // that can be removed
        val settings = goal.settings

        def clauseReducer(c : Conjunction) =
          if (!FormulaTask.isFunctionalityAxiom(c, settings) &&
                goal.reduceWithFacts.tentativeReduce(c).isFalse)
            Conjunction.FALSE
          else
            c
      
        // cached instances are only simplified using equational facts
        // (otherwise, we might prevent generation of genuine instances
        // later on)
        
        val instanceReducer = ReduceWithConjunction(
          Conjunction.conj(goal.facts.arithConj.positiveEqs, order), order)

        matcher.reduceClauses(clauseReducer _,
                              instanceReducer.tentativeReduce _,
                              order)
      } else {
        val reducerObj : Conjunction => Conjunction =
          goal.reduceWithFacts.tentativeReduce _
        matcher.reduceClauses(reducerObj, reducerObj, order)
      }

    val newTasks =
      goal formulaTasks Conjunction.negate(removedClauses, order)
    (reducedMatcher, newTasks)
  }

  private def disjPullOutAll(formulas : Iterable[Conjunction],
                             order : TermOrder) : Conjunction = {
    var nextVar = 0
    val body = Conjunction.disj(
      for (c <- formulas.iterator) yield {
        if (c.quans.lastOption == Some(Quantifier.ALL)) {
          val allNum = c.quans.size - c.quans.lastIndexOf(Quantifier.EX) - 1
          val newC = c.instantiate(for (i <- nextVar until (nextVar + allNum))
                                   yield VariableTerm(i))(order)
          nextVar = nextVar + allNum
          newC
        } else {
          c
        }
      }, order)
    Conjunction.quantify(for (_ <- 0 until nextVar) yield Quantifier.ALL,
                         body, order)
  }

}

////////////////////////////////////////////////////////////////////////////////

case object EagerMatchTask extends EagerTask {
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    MatchFunctions.updateMatcher(goal, ptf, true)
}

////////////////////////////////////////////////////////////////////////////////

object LazyMatchTask {
  
  private val AC = Debug.AC_CLAUSE_MATCHER
  
  def addTask(goal : Goal) : Seq[PrioritisedTask] =
    if (!goal.tasks.taskSummaryFor(TaskAggregator.LazyMatchTaskCounter).isEmpty)
      List()
    else
      List(new LazyMatchTask (goal.age,
                              Param.MATCHING_BASE_PRIORITY(goal.settings)))
}

class LazyMatchTask(age : Int, basePriority : Int)
      extends PrioritisedTask {
  
  val priority : Int = - basePriority + age

  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                : Seq[PrioritisedTask] = List(this)

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LazyMatchTask.AC,
                    !(goal.compoundFormulas.eagerQuantifiedClauses factsAreOutdated
                                                           goal.facts.predConj))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    MatchFunctions.updateMatcher(goal, ptf, false)
  }
  
  override def toString = "LazyMatchTask(" + priority + ")"
}
