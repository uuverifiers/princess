/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.HeapCollector
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap}

object TaskInfoCollector {
  
  def EMPTY(abbrevLabels : Map[Predicate, Predicate]) : TaskInfoCollector =
    new TaskInfoCollector(Set.empty, false, abbrevLabels, Set(), Set(), Map())
  
}

class TaskInfoCollector private
             (val constants : Set[ConstantTerm],
              val containsLazyMatchTask : Boolean,
              abbrevLabels : Map[Predicate, Predicate],
              val occurringAbbrevs : Set[Predicate],
              val occurringAbbrevDefs : Set[Predicate],
              val occurringBooleanVars : GMap[Predicate, Int])
      extends HeapCollector[Task, TaskInfoCollector] {

  def +(task : Task, otherInfos : TaskInfoCollector) : TaskInfoCollector = {
    val booleanVars : Set[Predicate] = task match {
      case task : FormulaTask =>
        task.formula.predicates filter (_.arity == 0)
      case _ =>
        Set.empty
    }

    val (taskConstants, newAbbrevs)
            : (Set[ConstantTerm], Set[Predicate]) = task match {
      case task : FormulaTask =>
        (task.formula.constants,
         if (abbrevLabels.isEmpty)
           Set.empty
         else
           booleanVars & abbrevLabels.keySet)
      case _ =>
        (Set.empty, Set.empty)
    }

    val newDefs : Set[Predicate] =
      if (newAbbrevs.isEmpty)
        Set.empty
      else task match {
        case task : BetaFormulaTask =>
          newAbbrevs filter {
            p => booleanVars contains abbrevLabels(p)
          }
        case task : WrappedFormulaTask
                        if (task.realTask.isInstanceOf[BetaFormulaTask]) =>
          newAbbrevs filter {
            p => booleanVars contains abbrevLabels(p)
          }
        case _ =>
          Set.empty
      }

    val newBooleanVarNums = new MHashMap[Predicate, Int]
    newBooleanVarNums ++= this.occurringBooleanVars
    for ((q, n) <- otherInfos.occurringBooleanVars)
      newBooleanVarNums.put(q, n + newBooleanVarNums.getOrElse(q, 0))
    for (q <- booleanVars)
      newBooleanVarNums.put(q, 1 + newBooleanVarNums.getOrElse(q, 0))

    new TaskInfoCollector(this.constants ++
                            taskConstants ++
                            otherInfos.constants,
                          this.containsLazyMatchTask ||
                            task.isInstanceOf[LazyMatchTask] ||
                            otherInfos.containsLazyMatchTask,
                          this.abbrevLabels,
                          this.occurringAbbrevs ++
                            (newAbbrevs -- newDefs) ++
                            otherInfos.occurringAbbrevs,
                          this.occurringAbbrevDefs ++
                            newDefs ++
                            otherInfos.occurringAbbrevDefs,
                          newBooleanVarNums)
  }
  
}
