/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.math.PartialOrdering
import scala.util.Random
import scala.collection.mutable.{BitSet => MBitSet, ArrayBuffer}

object POGraph {

  private val AC = Debug.AC_PO_GRAPH

}

/**
 * A class to explicitly represent partial orders. This is used in various
 * contexts to speed up implication checks.
 */
class POGraph[A](implicit ordering : PartialOrdering[A],
                          rand : Random) {

  private val elements = new ArrayBuffer[A]
  private val randomOrder = new ArrayBuffer[Int]
  private val predecessors, successors,
              directPredecessors, directSuccessors = new ArrayBuffer[MBitSet]

  /**
   * Add a new element to the graph.
   */
  def += (a : A) : Unit = {
    // compute predecessors/successors
    val preds, succs, directPreds, directSuccs = new MBitSet
    for (ind <- randomOrder) {
      if (!(preds contains ind) && !(succs contains ind)) {
        val el = elements(ind)
        ordering.tryCompare(el, a) match {
          case Some(r) =>
            if (r < 0) {
              val ps = predecessors(ind)
              preds += ind
              preds |= ps
              directPreds += ind
              directPreds &~= ps
            } else if (r > 0) {
              val ss = successors(ind)
              succs += ind
              succs |= ss
              directSuccs += ind
              directSuccs &~= ss
            } else {
              throw new Exception("tried to add element twice to PO graph")
            }
          case None =>
            // nothing to do
        }
      }
    }

    // adjust other edges to the new element
    val newInd = elements.size

    for (ind <- directPreds) {
      val ds = directSuccessors(ind)
      successors(ind) += newInd
      ds += newInd
      ds &~= directSuccs
    }

    for (ind <- directSuccs) {
      val dp = directPredecessors(ind)
      predecessors(ind) += newInd
      dp += newInd
      dp &~= directPreds
    }

    // insert all the new data
    elements           += a
    predecessors       += preds
    successors         += succs
    directPredecessors += directPreds
    directSuccessors   += directSuccs
    randomOrder.insert(rand nextInt (newInd + 1), newInd)
  }

}