/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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
