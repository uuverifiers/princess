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

import ap.connection.connection.{BREUOrder}
import ap.terfor.ConstantTerm
import ap.util.Debug
import scala.collection.mutable.ListBuffer


object ClosedStyle extends Enumeration {
  type ClosedStyle = Value
  val Strong, Weak, Open = Value
}

import ClosedStyle._

// TODO: Maybe store how branch was closed?
// This could be useful for reusing old solutions!
class ConnectionBranch(val nodes : List[Node], val closed : ClosedStyle, val order : BREUOrder) {

  // Output formatting helper methods
  // def longestPrefix(that : List[Node]) : List[Node] =
  //   (this.nodes zip that).takeWhile(x => x._1 == x._2).map(_._1)
  // def longestPrefix(that : ConnectionBranch) : List[Node] = 
  //   longestPrefix(that.nodes)

  override def toString = {
    val str =
      closed match {
        case ClosedStyle.Open => "  (---) " + nodes.mkString(", ") + " ! " + strongConnections.mkString(", ")
        case ClosedStyle.Strong => "  (STR) " + nodes.mkString(", ") + " @ " + strongConnections.mkString(", ")
        case ClosedStyle.Weak => "  (WEK) " + nodes.mkString(", ") + " @ " + weakConnections.mkString(", ")
      }
    str + " $" + order.mkString(",")
  }

  def isOpen = (closed == ClosedStyle.Open)
  def isStronglyClosed = (closed == ClosedStyle.Strong)
  def isWeaklyClosed = (closed == ClosedStyle.Weak)
  def closed(strong : Boolean) = 
    strong match {
      case true => new ConnectionBranch(nodes, Strong, order)
      case false => new ConnectionBranch(nodes, Weak, order)
    }

  def closedSafe(strong : Boolean)  : Option[ConnectionBranch] = {
    strong match {
      case true => {
        if (stronglyClosable) Some(closed(strong)) else None
      }
      case false => {
        if (weaklyClosable) Some(closed(strong)) else None
      }
    }
  }
  def depth = (for (n <- nodes if n.isLiteral) yield 1).sum
  def length = nodes.length
  def apply(idx : Int) = nodes(idx)

  // TODO: Extra order, yuck...
  def extend(literal : PseudoLiteral, extraOrder : BREUOrder) = {
    // TODO: Correct combination order?
    val mergeOrder = extraOrder ++ order
    new ConnectionBranch(literal.lit :: literal.funs ++ nodes, ClosedStyle.Open, mergeOrder)
  }

  def positiveLiterals = nodes.filter(_.isPositiveLiteral).map(_.asPositiveLiteral)
  def negativeLiterals = nodes.filter(_.isNegativeLiteral).map(_.asNegativeLiteral)  
  def equations = nodes.filter(_.isEquation).map(_.asEquation)
  def funEquations = nodes.filter(x => x.isFunEquation).map(_.asFunEquation)
  def negEquations = nodes.filter(_.isNegEquation).map(_.asNegEquation)


  val allConnections = {
    var connections = ListBuffer() : ListBuffer[Connection]
    // 
    // All connections
    //
    for (i <- 0 until nodes.length;
      j <- i + 1 until nodes.length;
      if (nodes(i).structuralUnifiable(nodes(j))))
      connections += ConnectionCompLits(i, j)

    for (negEq <- negEquations)
     connections += ConnectionNegEq(nodes indexOf negEq)

    connections.toList
  }

  val strongConnections = {
    var connections = ListBuffer() : ListBuffer[Connection]
    val nextLiteral = (nodes.tail indexWhere (_.isLiteral))+1
    if (nextLiteral >= 0  && nodes(0).structuralUnifiable(nodes(nextLiteral)))
      connections += ConnectionCompLits(0, nextLiteral)

    if (nodes(0).isNegEquation)
      connections += ConnectionNegEq(0)

    connections.toList
  }

  val weakConnections = {
    var connections = ListBuffer() : ListBuffer[Connection]
    //
    // Weak connections
    //
    for (i <- 1 until nodes.length;
      if (nodes(0).structuralUnifiable(nodes(i))))
      connections += ConnectionCompLits(0, i)

    if (nodes(0).isNegEquation)
      connections += ConnectionNegEq(0)

    connections.toList
  }

  val allClosable = allConnections.length > 0
  val weaklyClosable = weakConnections.length > 0
  val stronglyClosable = strongConnections.length > 0

  val closable = {
    closed match {
      case ClosedStyle.Open => false
      case ClosedStyle.Weak => weaklyClosable
      case ClosedStyle.Strong => stronglyClosable
    }
  }

  def toBREU : List[List[(ConstantTerm, ConstantTerm)]] = {
    val connections = 
      closed match {
        case ClosedStyle.Open => throw new Exception("toBREU on open branch")
        case ClosedStyle.Weak => weakConnections
        case ClosedStyle.Strong => strongConnections
      }

    (for (c <- connections) yield {
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
            case (pl : PositiveLiteral, nl : NegativeLiteral) =>
              for ((t1, t2) <- pl.args zip nl.args) yield (t1, t2)
            case (nl : NegativeLiteral, pl : PositiveLiteral) =>
              for ((t1, t2) <- pl.args zip nl.args) yield (t1, t2)
          }
              // val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
              // val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

              // (node1, node2)
              // for ((arg1, arg2) <- (pred1atom zip pred2atom).toList) yield {
              //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
              // Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
              //-END-ASSERTION-//////////////////////////////////////////////////////////
                // println("\t" + arg1 + "\t?=\t" + arg2)
                // println("\t" + arg1.getClass + " \t?=\t" + arg2.getClass)
                // (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
                // }
          //   case _ => throw new Exception("ConncetionCompLits is pointing wrong!")
          // }
        }
      }
    }).toList 
  }
}
