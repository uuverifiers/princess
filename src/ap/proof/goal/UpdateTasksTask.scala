/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal;

import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.parameters.Param
import ap.terfor.arithconj.{EquivModelElement, ElimPredModelElement}
import ap.terfor.preds.{Predicate, PredConj, Atom}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, Seqs}

import scala.collection.mutable.ArrayBuffer

/**
 * Meta-Task for updating all tasks of a goal
 */
case object UpdateTasksTask extends EagerTask {

  private val AC = Debug.AC_GOAL

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val oldTasks = goal.tasks
    val criticalPreds =
      goal.facts.predicates ++ goal.compoundFormulas.predicates

    // we might have to remove ourself from the task-manager
    val remTasks = if (oldTasks.max == this)
                     oldTasks.removeFirst
                   else
                     oldTasks

    val postProcessors = new ArrayBuffer[ProofTree => ProofTree]

    val newTasks =
      elimUnneededDefs(remTasks, criticalPreds, postProcessors, ptf)
    
    def stopUpdating(task : Task) = task match {
      case _ : AddFactsTask => true
      case WrappedFormulaTask(_, simpTasks) => simpTasks exists {
        case _ : AddFactsTask => true
        case _ => false
      }
      case _ => false
    }
    
    val newTasks2 =
      newTasks.updateTasks(goal, stopUpdating _)
    val newTasks3 =
      elimUnneededDefs(newTasks2, criticalPreds, postProcessors, ptf)

    (postProcessors :\ ptf.updateGoal(newTasks3, goal)) { case (f, t) => f(t) }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Identify tasks that represent equivalences of the form
   * <code>q <=> phi</code>, where <code>q</code> is a Boolean variable
   * that does not occur anywhere else in the proof. Such equivalences
   * can be eliminated, since they cannot contribute to closing a proof.
   */
  private def eliminableEquiv(task : PrioritisedTask,
                              eliminablePreds : Set[Predicate])
                              : Option[(Atom, Conjunction)] = task match {
    case task : BetaFormulaTask =>
      eliminableEquiv(task.formula, eliminablePreds)
    case WrappedFormulaTask(task : BetaFormulaTask, _) =>
      eliminableEquiv(task.formula, eliminablePreds)
    case _ => None
  }

  private def eliminableEquiv(formula : Conjunction,
                              eliminablePreds : Set[Predicate])
                              : Option[(Atom, Conjunction)] = {
    if (!formula.isPurelyNegated || formula.negatedConjs.size != 2)
      return None

    val left = formula.negatedConjs(0)
    val right = formula.negatedConjs(1)

    if (left.predConj.isTrue || right.predConj.isTrue)
      return None

    // for the formula to be an equivalence, one of the disjuncts
    // has to be a conjunction of the singleton variable and some
    // other formula; i.e., have size 2
    if (left.size != 2 && right.size != 2)
      return None

    // case that is currently not supported
    if (formula.predicates exists (_.arity > 0))
      return None

    val singletonVars =
      (left.predConj.positiveLits.iterator filter { a =>
         val p = a.pred
         p.arity == 0 &&
         (eliminablePreds contains p) &&
         !right.predConj.negativeLitsWithPred(p).isEmpty
       }) ++
      (left.predConj.negativeLits.iterator filter { a =>
         val p = a.pred
         p.arity == 0 &&
         (eliminablePreds contains p) &&
         !right.predConj.positiveLitsWithPred(p).isEmpty
       })

    while (singletonVars.hasNext) {
      val singletonVar = singletonVars.next

      implicit val order = formula.order

      val remainingLeftPredConj =
        left.predConj.updateLitsSubset(
          left.predConj.positiveLits filterNot (_ == singletonVar),
          left.predConj.negativeLits filterNot (_ == singletonVar),
          order)
      val remainingLeft = left.updatePredConj(remainingLeftPredConj)

      val remainingRightPredConj =
        right.predConj.updateLitsSubset(
          right.predConj.positiveLits filterNot (_ == singletonVar),
          right.predConj.negativeLits filterNot (_ == singletonVar),
          order)
      val remainingRight = right.updatePredConj(remainingRightPredConj)

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // the singleton variable should have been eliminated from the
      // rest of the formula at an earlier point
      Debug.assertInt(AC,
        !(remainingLeft.predicates contains singletonVar.pred) &&
        !(remainingRight.predicates contains singletonVar.pred))
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      if (remainingLeft == remainingRight.negate) {
        // found an equivalence that can be eliminated!
//        println("eliminating ... " + formula)

        val singletonDef =
          if (left.predConj.positiveLitsAsSet contains singletonVar)
            remainingLeft
          else
            remainingRight
//        println("" + singletonVar + " := " + singletonDef)

        return Some((singletonVar, singletonDef))
      }
    }

    None
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Possibly remove abbreviations that are not needed anymore
   */
  private def elimUnneededDefs(
           tasks : TaskManager,
           criticalPreds : Set[Predicate],
           postProcs : ArrayBuffer[ProofTree => ProofTree],
           ptf : ProofTreeFactory) : TaskManager = {
    val eliminableBooleanVars =
      (for ((p, n) <- tasks.taskInfos.occurringBooleanVars.iterator;
            if (n == 1 && !(criticalPreds contains p)))
       yield p).toSet

    val danglingAbbrevDefs = 
      tasks.taskInfos.occurringAbbrevDefs filterNot {
        p => (tasks.taskInfos.occurringAbbrevs contains p) ||
             (criticalPreds contains p)
      }
    
    if (danglingAbbrevDefs.isEmpty && eliminableBooleanVars.isEmpty) {
      tasks
    } else {
      var collectedVarDefs = List[(Atom, Conjunction)]()
      var collectedAbbrevs = Set[Predicate]()

      val newTasks = tasks filter {
        case t : FormulaTask =>
          if (Seqs.disjoint(danglingAbbrevDefs, t.formula.predicates)) {
            eliminableEquiv(t, eliminableBooleanVars) match {
              case Some(p) => {
                // an equivalence has been found that can be eliminated
                collectedVarDefs = p :: collectedVarDefs
                false
              }
              case None =>
                true
            }
          } else {
            // this formula is the definition of an abbreviation
            // that is no longer needed
            collectedAbbrevs =
              collectedAbbrevs ++ (danglingAbbrevDefs & t.formula.predicates)
            false
          }
        case _ =>
          true
      }

      if (collectedVarDefs.isEmpty && collectedAbbrevs.isEmpty) {
        tasks
      } else {
        if (!collectedVarDefs.isEmpty)
          postProcs +=
            ((p:ProofTree) => ptf.eliminatedConstant(p,
                                EquivModelElement(collectedVarDefs.reverse),
                                p.vocabulary))
        if (!collectedAbbrevs.isEmpty)
          postProcs +=
            ((p:ProofTree) => ptf.eliminatedConstant(p,
                                ElimPredModelElement(collectedAbbrevs),
                                p.vocabulary))
        elimUnneededDefs(newTasks, criticalPreds, postProcs, ptf)
      }
    }
  }

}
