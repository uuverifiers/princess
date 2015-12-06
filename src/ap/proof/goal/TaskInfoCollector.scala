/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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
