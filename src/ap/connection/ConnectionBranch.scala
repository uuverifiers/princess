/**
 * This file is part of ePrincess, a theorem prover based on 
 * Bounded Rigid E-Unification (http://user.it.uu.se/~petba168/breu/) 
 * incoporated into the Princess theorem prover
 * <http://www.philipp.ruemmer.org/princess.shtml>
 * 
 * Copyright (C) 2009-2016 Peter Backeman <peter@backeman.se>
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * ePrincess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ePrincess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with ePrincess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.connection;

import ap.connection.connection.{OrderNode, BREUOrder}
import ap.terfor.ConstantTerm
import ap.util.Debug
import scala.collection.mutable.ListBuffer

// TODO: Maybe store how branch was closed?
// This could be useful for reusing old solutions!
class ConnectionBranch(val nodes : List[Node], val open : Boolean, val order : BREUOrder) {

  override def toString = {
    if (open) {
        "||\t (---) " + nodes.mkString(", ")
    } else {
        "||\t (XXX) " + nodes.mkString(", ")
    }
  }

  def isOpen = open
  def closed = new ConnectionBranch(nodes, false, order)
  def depth = (for (n <- nodes if n.isLiteral) yield 1).sum
  def length = nodes.length
  def apply(idx : Int) = nodes(idx)

  // TODO: Extra order, yuck...
  def extend(newOrderNode : OrderNode, extraOrder : BREUOrder) = {
    val (newNodes, newOrder) = newOrderNode
    // TODO: Correct combination order?
    val mergeOrder = newOrder ++ extraOrder ++ order
    new ConnectionBranch(newNodes ++ nodes, open, mergeOrder)
  }

  def literals = nodes.filter(_.isLiteral).map(_.asLiteral)
  def equations = nodes.filter(_.isEquation).map(_.asEquation)
  def funEquations = nodes.filter(_.isFunEquation).map(_.asFunEquation)
  def negEquations = nodes.filter(_.isNegEquation).map(_.asNegEquation)
  def negFunEquations = nodes.filter(_.isNegFunEquation).map(_.asNegFunEquation)

  val connections = {
    var connections = ListBuffer() : ListBuffer[Connection]

    for (i <- 0 until nodes.length;
      j <- i + 1 until nodes.length;
      if (nodes(i).structuralUnifiable(nodes(j))))
    yield connections += ConnectionCompLits(i, j)

    for (negEq <- negEquations) {
      connections += ConnectionNegEq(nodes indexOf negEq)
    }

    connections.toList
  }

  val structuralClosable = connections.length > 0


  // TODO: Maybe get rid of  Connection data structure completely?
  def connectionToBREU(c : Connection) = {
    c match {
      case ConnectionNegEq(node) => {
        (nodes(node)) match {
          case (NegEquation(t1, t2)) => {
            List((t1, t2))
          }
          case _ => throw new Exception("ConnectionNegEq is pointing wrong!")
        }
      }
      case ConnectionCompLits(node1, node2) => {
        (nodes(node1), nodes(node2)) match {
          case (Literal(pred1), Literal(pred2)) => {
            val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
            val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

            for ((arg1, arg2) <- (pred1atom zip pred2atom).toList) yield {
              //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
              Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
              //-END-ASSERTION-//////////////////////////////////////////////////////////
              // println("\t" + arg1 + "\t?=\t" + arg2)
              // println("\t" + arg1.getClass + " \t?=\t" + arg2.getClass)
              (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
            }
          }
          case _ => throw new Exception("ConncetionCompLits is pointing wrong!")
        }
      }
    }
  }
}
