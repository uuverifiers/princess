/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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
