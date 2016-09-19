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

import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.util.{Debug, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.connection.connection._

import scala.collection.mutable.{Map => MMap}

class ConnectionTable(private val branches : Seq[ConnectionBranch], preSettings : GoalSettings) {

  // TODO: Make nicer?
  var nextPredicate = 0

  def longestPrefix(nodeLists : Seq[Seq[Node]])  = {
    if (nodeLists.isEmpty) {
      0
    } else {
      val head = nodeLists.head

      def isPrefix(pre : Seq[Node]) : Boolean = {
        // println("isPrefix(" + pre + ") of " + nodeLists.mkString(","))
        for (nodes <- nodeLists) {
          for ((n1,n2) <- nodes zip pre)
            if (n1 != n2) {
              // println("\tNo")
              return false
            }
        }
        // println("\tYes")
        return true
      }

      var prefixLength = 0
      while (isPrefix(head.take(prefixLength)) && prefixLength <= head.length) {
        prefixLength += 1
      }
      prefixLength - 1
    }
  }

  override def toString = {

    def printBranch(nodeLists : Seq[(Seq[Node], ClosedStyle.ClosedStyle)], level : Int, branch : List[Int]) : String = {
      if (!nodeLists.isEmpty) {
        val head = nodeLists.head._1
        val tabs = "\t" * level
        // i: how many branches has the same prefix
        var i = nodeLists.length
        while (i > 0) {
          val nls = nodeLists.take(i)
          val lp = longestPrefix(nls.map(_._1))
          if (lp > 0) {
            val thisStr = 
              tabs + "Branch: " + branch.reverse.mkString(".") + "\n " + (for (n <- head.take(lp)) yield (tabs + n)).mkString("\n")
            // Divide and Conquer
            val rec1 = printBranch(nls.map(x => (x._1.drop(lp), x._2)), level+1, 1 :: branch)
            val rec2 = printBranch(nodeLists.drop(i), level, (branch.head + 1) :: branch.tail)
            return thisStr + "\n" + rec1 + rec2
          }
          i -= 1
        }

        val closer = 
          nodeLists.head._2 match {
            case ClosedStyle.Open => "--OPEN--"
            case ClosedStyle.Strong => "-STRONG-"
            case ClosedStyle.Weak => "--WEAK--"
          }
        tabs + closer + "\n" + printBranch(nodeLists.tail, level, (branch.head + 1) :: branch.tail)
      } else {
        ""
      }
    }

    printBranch(branches.map(x => (x.nodes.reverse, x.closed)), 0, List(1))
    
  }
  def width = branches.length
  def openBranches = branches.count(_.isOpen)
  def isOpen = openBranches > 0

  // Extend branch branchIdx with clause(idx) and add new branches to the right
  def extendBranch(branchIdx : Int, orderClause : OrderClause, idx : Int, newOrder : BREUOrder) = {
    val preBranches = branches.take(branchIdx)
    val postBranches = branches.drop(branchIdx + 1)
    val newBranches = for (c <- orderClause) yield branches(branchIdx).extend(c, newOrder)
    new ConnectionTable(preBranches ++ (newBranches(idx) :: newBranches.filter(_ != newBranches(idx)))  ++ postBranches, preSettings)
  }

  def close(idx : Int, strong : Boolean) : ConnectionTable = {
    val newBranches =
      for (i <- 0 until branches.length) yield {
        if (i == idx)
          branches(i).closed(strong)
        else
          branches(i)
      }
    new ConnectionTable(newBranches, preSettings)
  }

  def closeSafe(idx : Int, strong : Boolean) : Option[ConnectionTable] = {
    val breuSolver = new breu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    val closeBranch = branches(idx).closedSafe(strong)
    if (closeBranch.isEmpty) {
      None
    } else {
      val problem = branchToBREU(breuSolver, List(closeBranch.get))
      ap.util.Timer.measure("BREU") {
        if (problem.solve == breu.Result.SAT) {
          Some(close(idx, strong))
        } else {
          None
        }
      }
    }
  }

  def unifyBranches() 
      : (Option[Map[ConstantTerm, ConstantTerm]]) = {
    val breuSolver = new breu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    val problem = branchToBREU(breuSolver)
    ap.util.Timer.measure("BREU") {
      if (problem.solve == breu.Result.SAT) {
        Some(problem.getModel)
      } else {
        None
      }
    }
  }

  def closable : Boolean = 
    !(branches.find(b => !b.isOpen && !b.closable).isDefined) &&
    unifyBranches().isDefined

  // PRE: must be one open branch
  def firstOpen = {
    val first = branches.find(_.isOpen)
    val idx = branches indexOf first
    (first, idx)
  }

  def shortestOpen = {
    val openBranches = branches.filter(_.isOpen)
    val shortestOpen = openBranches.minBy(_.length)
    val idx = branches indexOf shortestOpen
    (shortestOpen, idx)
  }


  def combineOrders(orders : Seq[BREUOrder]) = {
    val maps = orders.map(orderToMap)
    val keys : Set[ConstantTerm] = (for (m <- maps) yield m.keys).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
    for (k <- keys) yield {
      val allVals : Set[ConstantTerm] = (for (m <- maps) yield { m.getOrElse(k, Set() : Set[ConstantTerm]) }).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
      (k -> allVals)
    }
  }

  def orderToMap(order : BREUOrder) = {
      val domain = MMap() : MMap[ConstantTerm,Set[ConstantTerm]]
      for ((t, uni) <- order.reverse) {
        domain += (t -> Set(t))
        if (uni) {
          for (k <- domain.keys) {
            domain += (t -> (domain(t) + k))
          }
        }
      }
    domain
  }


  def convertFunEquation(funEq : FunEquation) = {
    val pc = funEq.eq
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
  }


  def convertNegFunEquation(negFunEq : NegFunEquation) = {
    val pc = negFunEq.eq
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
  }


  def convertEquation(eq : Equation) = {
    eq match {
      case Equation(lhs, rhs) => {
        val p = new Predicate("DummyPredicate" + nextPredicate, 0)
        nextPredicate += 1
        List((p, List(), lhs), (p, List(), rhs))
      }
    }
  }


  def branchToBREU(breuSolver : breu.BREUSolver[ConstantTerm, Predicate], breuBranches : Seq[ConnectionBranch])
      : breu.BREUInstance[ConstantTerm, Predicate]  = {
    // We need to keep track of domains

    val domains = combineOrders(for (branch <- breuBranches) yield branch.order)

    val subProblems =
      for (branch <- breuBranches) yield {
        if (!branch.allClosable) {
          throw new Exception("Trying to create BREU-problem from structural open branch!")
        } else {
          val funEqs = branch.funEquations.map(convertFunEquation(_))
          val eqs = branch.equations.map(convertEquation(_)).flatten
          val negFunEqs = branch.negFunEquations.map(convertNegFunEquation(_))
          
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
          //-END-ASSERTION-//////////////////////////////////////////////////////////

          val argGoals : List[List[(ConstantTerm, ConstantTerm)]] = branch.toBREU
          (argGoals.toList, funEqs ++ eqs, negFunEqs)
        }
      }
    breuSolver.createProblem(domains.toMap, subProblems.map(_._1), subProblems.map(_._2), subProblems.map(_._3))
  }

  def branchToBREU(breuSolver : breu.BREUSolver[ConstantTerm, Predicate]) 
      : breu.BREUInstance[ConstantTerm, Predicate]  = {
    val closedBranches = branches.filter(!_.isOpen)
    branchToBREU(breuSolver, closedBranches)
  }
}
