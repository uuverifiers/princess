/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.goal

import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.Vocabulary
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.{ConstantTerm, VariableTerm, TermOrder}
import ap.parameters.Param
import ap.util.Debug

import scala.collection.mutable.ArrayBuffer

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
    val order = goal.order
    val collector = goal.getInferenceCollector
    val oldMatcher = goal.compoundFormulas quantifierClauses eager

    // first check whether any of the clauses has to be updated
    val (removedClauses, reducedMatcher) =
      if (collector.isLogging) {
        // if we are producing proofs, we mostly check for subsumed clauses
        // that can be removed

        def clauseReducer(c : Conjunction) =
          if (goal.reduceWithFacts.tentativeReduce(c).isFalse)
            Conjunction.FALSE
          else
            c
      
        // cached instances are only simplified using equational facts
        // (otherwise, we might prevent generation of genuine instances
        // later on)
        
        val instanceReducer = ReduceWithConjunction(
          Conjunction.conj(goal.facts.arithConj.positiveEqs, order),
          Param.FINITE_DOMAIN_CONSTRAINTS.assumeInfiniteDomain(goal.settings),
          order)
          
        oldMatcher.reduceClauses(clauseReducer _,
                                 instanceReducer.tentativeReduce _,
                                 order)
      } else {
        val reducerObj : Conjunction => Conjunction =
          goal.reduceWithFacts.tentativeReduce _
        oldMatcher.reduceClauses(reducerObj, reducerObj, order)
      }

    if (removedClauses.isEmpty) {
      val voc = goal.vocabulary
  
      val reverseProp = Param.REVERSE_FUNCTIONALITY_PROPAGATION(goal.settings)
      val (instances, newMatcher) =
        reducedMatcher.updateFacts(goal.facts.predConj,
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

      val newCF = goal.compoundFormulas.updateQuantifierClauses(eager, newMatcher)
      val newTasks =
        if (collector.isLogging)
          // if we are producing proofs, we have to treat the instances
          // separately (to log all performed simplifications)
          for (f <- normalInstances; t <- goal.formulaTasks(f)) yield t
        else
          for (t <- goal.formulaTasks(
                 goal reduceWithFacts disjPullOutAll(normalInstances, order))) yield t

      ptf.updateGoal(newCF, newTasks ++ blockedTasks, collector.getCollection, goal)
    } else {
      val newTasks =
        (goal formulaTasks Conjunction.negate(removedClauses, order)) ++
        (if (eager)
           List()
         else
           List(new LazyMatchTask (goal.age, Param.MATCHING_BASE_PRIORITY(goal.settings))))
      val newCF = goal.compoundFormulas.updateQuantifierClauses(eager, reducedMatcher)
      ptf.updateGoal(newCF, newTasks, collector.getCollection, goal)
    }
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
    if (goal.tasks.taskInfos.containsLazyMatchTask)
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
