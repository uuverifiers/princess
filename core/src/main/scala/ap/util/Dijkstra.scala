/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2021-2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.{Tree, Leaf}

import scala.collection.mutable.{HashMap => MHashMap, PriorityQueue}

object Dijkstra {

  trait WeightedGraph[Node] {
    def successors(n : Node) : Iterator[(Node, Int)]
  }

  /**
   * The tree formed by the shortest paths from the source to all
   * reachable nodes. Note that, while the distances of nodes from
   * the source are uniquely defined, the shortest paths are not, and
   * therefore also the computed tree will not be deterministic.
   */
  def shortestPathTree[Node](graph : WeightedGraph[Node],
                             source : Node) : Tree[(Node, Int)] =
    (new Dijkstra (graph, source)).shortestPathTree

  /**
   * The distances of all reachable nodes from the source.
   */
  def distances[Node](graph : WeightedGraph[Node],
                      source : Node) : Map[Node, Int] =
    (new Dijkstra (graph, source)).distances

/*
  def main(args : Array[String]) : Unit = {
    println("Computing shortest paths ...")

    val graph = new WeightedGraph[Int] {
      def successors(n : Int) = n match {
        case 0 => Iterator((0, 1), (1, 1), (3, 20))
        case 1 => Iterator((2, 3))
        case 2 => Iterator((3, 1))
        case 3 => Iterator((3, 1), (1, 1))
      }
    }

    val t = new Dijkstra (graph, 0)
    println("Result:")
    println(t.distances)
    t.shortestPathTree.prettyPrint
  }
 */
}

/**
 * An implementation of Dijkstra's algorithm for computing shortest
 * paths to all reachable nodes in a graph.
 */
class Dijkstra[Node] (graph : Dijkstra.WeightedGraph[Node],
                      source : Node) {

  private implicit val pairOrder : Ordering[(Int, Node)] =
    Ordering.by[(Int, Node), Int] { p => -p._1 }

  private val todo = new PriorityQueue[(Int, Node)]
  private val dist = new MHashMap[Node, Int]
  private val prev = new MHashMap[Node, Node]

  todo.enqueue((0, source))
  dist.put(source, 0)

  while (!todo.isEmpty) {
    val p@(nextDist, next) = todo.dequeue

    if (nextDist == dist(next))
      for ((s, w) <- graph successors next) {
        val d = nextDist + w
        (dist get s) match {
          case Some(oldD) if oldD <= d => // nothing
          case _ => {
            dist.put(s, d)
            prev.put(s, next)
            todo.enqueue((d, s))
          }
        }
      }
  }

  /**
   * The distances of all reachable nodes from the source.
   */
  lazy val distances : Map[Node, Int] = dist.toMap

  /**
   * The tree formed by the shortest paths from the source to all
   * reachable nodes. Note that, while the distances of nodes from
   * the source are uniquely defined, the shortest paths are not, and
   * therefore also the computed tree will not be deterministic.
   */
  lazy val shortestPathTree : Tree[(Node, Int)] = {
    val children = prev.toSeq groupBy (_._2)

    def subtree(n : Node) : Tree[(Node, Int)] =
      (children get n) match {
        case Some(pairs) =>
          Tree((n, dist(n)), for ((n2, _) <- pairs.toList) yield subtree(n2))
        case None =>
          Leaf((n, dist(n)))
      }

    subtree(source)
  }

}
