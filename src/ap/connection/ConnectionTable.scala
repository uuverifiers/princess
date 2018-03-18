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

import scala.collection.mutable.{Map => MMap, ListBuffer}

// TODO: branches should be private...
class ConnectionTable(val branches : Seq[ConnectionBranch], preSettings : GoalSettings, var DEBUG : Boolean = false) {

  // TODO: Make nicer?
  var nextPredicate = 0
  val diseqPairs = ListBuffer() : ListBuffer[(ConstantTerm, ConstantTerm)]

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
            case ClosedStyle.Strong => "-STRONG- "
            case ClosedStyle.Weak => "--WEAK--"
          }
        tabs + closer + "\n" + printBranch(nodeLists.tail, level, (branch.head + 1) :: branch.tail)
      } else {
        ""
      }
    }

    printBranch(branches.map(x => (x.nodes.reverse, x.closed)), 0, List(1))
    
  }


  // override def toString = {
  //   (for (b <- branches) yield 
  //     b.toString).mkString("\n")
  // }


  def width = branches.length
  def openBranches = branches.count(_.isOpen)
  def isOpen = openBranches > 0

  // Extend branch branchIdx with clause(idx) and add new branches to the right
  def extendBranch(branchIdx : Int, clause : PseudoClause, idx : Int, newOrder : BREUOrder) = {
    val preBranches = branches.take(branchIdx)
    val postBranches = branches.drop(branchIdx + 1)
    val newBranches = (for (c <- clause.pseudoLiterals) yield branches(branchIdx).extend(c, newOrder)).toList
    new ConnectionTable(preBranches ++ (newBranches(idx) :: newBranches.filter(_ != newBranches(idx)))  ++ postBranches, preSettings)
  }

  def close(idx : Int, strong : Boolean) : ConnectionTable = {
    val newBranches =
      for (i <- 0 until branches.length) yield {
        if (i == idx) {
          branches(i).closed(strong)
        } else {
          branches(i)
        }
      }
    new ConnectionTable(newBranches, preSettings)
  }


  /*
   * Converts branch idx to BREU and tries to close it in strong manner. 
   * 
   */
  // TODO: Should we have disequalities here?
  def closeSafe(idx : Int, strong : Boolean) : Option[ConnectionTable] = {
    val breuSolver = new breu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    val closeBranch = branches(idx).closedSafe(strong)
    if (closeBranch.isEmpty) {
      None
    } else {
      val problem = branchToBREU(breuSolver, List(closeBranch.get), List())
      ap.util.Timer.measure("BREU") {
        val result = problem.solve

        if (result == breu.Result.SAT) {
          Some(close(idx, strong))
        } else {
          None
        }
      }
    }
  }

  def unifyBranches(disequalities : Seq[(ConstantTerm, ConstantTerm)])
      : (Option[Map[ConstantTerm, ConstantTerm]]) = {

    val breuSolver = new breu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    val problem = branchToBREU(breuSolver, disequalities)
    if (DEBUG)
      println(problem)
    // problem.saveToFile("error.breu")
    val result = problem.solve
    // println("Blocking Unit Clauses:")
    for ((i1, i2) <- breuSolver.unitBlockingClauses) {
      val t1 = problem.intToTerm(i1)
      val t2 = problem.intToTerm(i2)
      diseqPairs += ((t1, t2))
      // println("\t" + ((i1, i2)) + " => " + ((t1, t2)))
    }

    ap.util.Timer.measure("BREU") {
      if (result == breu.Result.SAT) {
        Some(problem.getModel)
      } else {
        None
      }
    }
  }

  def unifyBranches() : (Option[Map[ConstantTerm, ConstantTerm]]) = unifyBranches(List())  

  def closable : Boolean = 
    !(branches.find(b => !b.isOpen && !b.closable).isDefined) && unifyBranches().isDefined

  def closable(disequalities : Seq[(ConstantTerm, ConstantTerm)]) : Boolean = 
    !(branches.find(b => !b.isOpen && !b.closable).isDefined) &&
    unifyBranches(disequalities).isDefined  

  // PRE: must be one open branch
  def firstOpen = {
    val first = branches.find(_.isOpen)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, first.isDefined)
    //-END-ASSERTION-//////////////////////////////////////////////////////////    
    branches indexOf first.get
  }

  def shortestOpen = {
    val openBranches = branches.filter(_.isOpen)
    val shortestOpen = openBranches.minBy(_.length)
    branches indexOf shortestOpen
  }


  /**
    * Combine orders from different branches into domains
    * 
    * The issue is when one variable occurs in several branches,
    * then the domain should be the intersection of its
    * domain on each branch.
    */
  def combineOrders(orders : Seq[BREUOrder], disequalities : Seq[(ConstantTerm, ConstantTerm)]) = {
    val maps = orders.map(orderToMap)
    val keys : Set[ConstantTerm] = (for (m <- maps) yield m.keys).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)

    val finalDomains = 
      (for (k <- keys) yield {
        val allVals : Set[ConstantTerm] = (for (m <- maps) yield { m.getOrElse(k, Set() : Set[ConstantTerm]) }).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
        (k -> allVals)
      }).toMap

    def isInDomain(x : (ConstantTerm, ConstantTerm)) = {
      val (s, t) = x
      finalDomains(s) contains t
    }

    val singleDomains = (disequalities.map(_.swap) ++ disequalities).filter(isInDomain).toMap
    // println("CombineOrder(" + orders + ", " + disequalities + ")")

    val newDomains =
      (for ((k, vals) <- finalDomains) yield {
        if (singleDomains contains k)
          (k, Set(singleDomains(k)))
        else
          (k, vals)
      }).toMap


    newDomains
    // finalDomains
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
    val atom = funEq.eq
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
  }


  // def convertNegFunEquation(negFunEq : NegFunEquation) = {
  //   val pc = negFunEq.eq
  //   //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //   Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
  //   //-END-ASSERTION-//////////////////////////////////////////////////////////
  //   val atom = pc.positiveLits(0)
  //   val fun = atom.pred
  //   val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
  //   val res = atom(atom.length-1).lastTerm.constants.head
  //   (fun, args.toList, res)
  // }


  def convertEquation(eq : Equation) = {
    eq match {
      case Equation(lhs, rhs) => {
        val p = new Predicate("DummyPredicate" + nextPredicate, 0)
        nextPredicate += 1
        List((p, List(), lhs), (p, List(), rhs))
      }
    }
  }


  def branchToBREU(breuSolver : breu.BREUSolver[ConstantTerm, Predicate], breuBranches : Seq[ConnectionBranch], disequalities : Seq[(ConstantTerm, ConstantTerm)])
      : breu.BREUInstance[ConstantTerm, Predicate]  = {
    // We need to keep track of domains
    val domains = combineOrders(for (branch <- breuBranches) yield branch.order, disequalities)

    val subProblems =
      for (branch <- breuBranches) yield {
        if (!branch.allClosable) {
          throw new Exception("Trying to create BREU-problem from structural open branch!")
        } else {
          val funEqs = branch.funEquations.map(convertFunEquation)
          val eqs = branch.equations.map(convertEquation).flatten
          val argGoals : List[List[(ConstantTerm, ConstantTerm)]] = branch.toBREU
          (argGoals.toList, funEqs ++ eqs)
        }
      }

    // TODO: BreuSolver takes neg fun eqs?
    val negFunEqs = for (_ <- subProblems) yield List()
    breuSolver.createProblem(domains.toMap, subProblems.map(_._1), subProblems.map(_._2), negFunEqs)
  }

  // TODO: Maybe we can replace with default arguments instead...
  // TODO: Make datatype for disequalities

  def branchToBREU(breuSolver : breu.BREUSolver[ConstantTerm, Predicate], disequalities : Seq[(ConstantTerm, ConstantTerm)])
      : breu.BREUInstance[ConstantTerm, Predicate]  = {
    val closedBranches = branches.filter(!_.isOpen)
    branchToBREU(breuSolver, closedBranches, disequalities)
  }
}
