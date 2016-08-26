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

  override def toString = branches.mkString("\n")
  def width = branches.length
  def isOpen = branches.find(_.isOpen).isDefined

  // Extend branch branchIdx with clause(idx) and add new branches to the right
  def extendBranch(branchIdx : Int, orderClause : OrderClause, idx : Int, newOrder : BREUOrder) = {
    val preBranches = branches.take(branchIdx)
    val postBranches = branches.drop(branchIdx + 1)
    val newBranches = for (c <- orderClause) yield branches(branchIdx).extend(c, newOrder)
    new ConnectionTable(preBranches ++ (newBranches(idx) :: newBranches.filter(_ != newBranches(idx)))  ++ postBranches, preSettings)
  }

  def close(idx : Int) = {
    val newBranches =
      for (i <- 0 until branches.length) yield {
        if (i == idx)
          branches(i).closed
        else
          branches(i)
      }
    new ConnectionTable(newBranches, preSettings)
  }

  def unifyBranches() 
      : (Option[Map[ConstantTerm, ConstantTerm]]) = {
    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    val problem = branchToBreu(ccuSolver)

    if (problem.solve == ccu.Result.SAT)
      Some(problem.getModel)
    else
      None
  }

  def closable : Boolean = 
    !(branches.find(b => !b.isOpen && !b.structuralClosable).isDefined) &&
    unifyBranches().isDefined

  def firstOpen = {
    val first = branches.find(_.isOpen)
    val idx = if (!first.isEmpty) (branches indexOf first.get) else -1
    (first, idx)
  }

  def combineOrders(orders : Seq[BREUOrder]) = {
    val maps = orders.map(orderToMap)
    val keys : Set[ConstantTerm] = (for (m <- maps) yield m.keys).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
    val domains = 
      for (k <- keys) yield {
        val allVals : Set[ConstantTerm] = (for (m <- maps) yield { m.getOrElse(k, Set() : Set[ConstantTerm]) }).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
        (k -> allVals)
      }
    domains
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

  def branchToBreu(ccuSolver : ccu.CCUSolver[ConstantTerm, Predicate])
      : ccu.CCUInstance[ConstantTerm, Predicate]  = {
    // We need to keep track of domains
    val closedBranches = branches.filter(!_.isOpen)
    val domains = combineOrders(for (branch <- closedBranches) yield branch.order)

    val subProblems =
      for (branch <- closedBranches) yield {
        if (!branch.structuralClosable) {
          throw new Exception("Trying to create BREU-problem from structural open branch!")
        } else {
          val funEqs = branch.funEquations.map(convertFunEquation(_))
          val eqs = branch.equations.map(convertEquation(_)).flatten
          val negFunEqs = branch.negFunEquations.map(convertNegFunEquation(_))
          
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
          //-END-ASSERTION-//////////////////////////////////////////////////////////

          val argGoals : List[List[(ConstantTerm, ConstantTerm)]] =
            for (c <- branch.connections) yield {
              branch.connectionToBREU(c)
            }
          (argGoals.toList, funEqs ++ eqs, negFunEqs)
        }
      }
    ccuSolver.createProblem(domains.toMap, subProblems.map(_._1), subProblems.map(_._2), subProblems.map(_._3))
  }
}
