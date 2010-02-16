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

package ap.proof.goal;

import ap.basetypes.HeapCollector
import ap.terfor.ConstantTerm

object TaskInfoCollector {
  
  val EMPTY : TaskInfoCollector = new TaskInfoCollector(Set.empty, false)
  
}

class TaskInfoCollector private (val constants : Set[ConstantTerm],
                                 val containsLazyMatchTask : Boolean)
      extends HeapCollector[Task, TaskInfoCollector] {

  def +(task : Task, otherInfos : TaskInfoCollector) : TaskInfoCollector = {
    val taskConstants = task match {
                          case task : FormulaTask => task.formula.constants
                          case _ => Set.empty 
                        }
    new TaskInfoCollector(this.constants ++ taskConstants ++ otherInfos.constants,
                          this.containsLazyMatchTask ||
                            task.isInstanceOf[LazyMatchTask] ||
                            otherInfos.containsLazyMatchTask)
  }
  
}
