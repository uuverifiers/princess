/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util

import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

object Tarjan {

  trait Graph[Node] {
    val nodes : Iterable[Node]
    def successors(n : Node) : Iterator[Node]
  }

  def apply[Node](graph : Graph[Node]) : IndexedSeq[Seq[Node]] =
    (new Tarjan (graph)).components

  /*
  def main(args : Array[String]) : Unit = {
    println("Computing strongly connected components ...")

    val graph = new Graph[Int] {
      val nodes = List(0, 1, 2, 3)
      def successors(n : Int) = n match {
        case 0 => Iterator(0, 1)
        case 1 => Iterator(2)
        case 2 => Iterator(1, 3)
        case 3 => Iterator(3, 1)
      }
    }

    val t = new Tarjan (graph)
    println(t.components)
  }
  */

}

/**
 * An implementation of Tarjan's algorithm for computing the strongly
 * connected components of a graph.
 */
class Tarjan[Node] (graph : Tarjan.Graph[Node]) {

  private val index, lowlink = new MHashMap[Node, Int]
  private val stack          = new LinkedHashSet[Node]
  private val componentsBuf  = new ArrayBuffer[Seq[Node]]

  private def connect(v : Node) : Unit = {
    val vIndex = index.size
    index.put(v, vIndex)
    lowlink.put(v, vIndex)
    stack += v

    for (w <- graph.successors(v))
      (index get w) match {
        case Some(wIndex) =>
          if (stack contains w)
            lowlink.put(v, lowlink(v) min index(w))
        case None => {
          connect(w)
          lowlink.put(v, lowlink(v) min lowlink(w))
        }
      }

    if (lowlink(v) == vIndex) {
      // found a strongly connected component
      val component = new VectorBuilder[Node]

      var next = stack.last
      stack remove next
      component += next
      while (next != v) {
        next = stack.last
        stack remove next
        component += next
      }

      componentsBuf += component.result
    }
  }

  for (v <- graph.nodes)
    if (!(index contains v))
      connect(v)

  /**
   * The result of the computation: the SCCs of the graph in
   * topological order.
   */
  val components = componentsBuf.reverse.toIndexedSeq

}
