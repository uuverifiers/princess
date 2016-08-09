//
// Todo:
// 
// Make NegFunEquation just Equation with polarity?
// Line 705 fix on geo118+1.p
// TODO: Fix terms vs order (BREUterms?)



/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Peter Backeman <peter.backeman@it.uu.se>
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.connection;

import ap._
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, NegatedConjunctions}
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.terfor.equations.EquationConj
import ap.terfor.arithconj.{ArithConj, ModelElement, EqModelElement}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience
import ap.proof.goal._
import ap.proof.certificates._
import ap.util.{Logic, Debug, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._
import ap.proof.{Vocabulary, ProofGrounder, ProofMinimiser, ConstantFreedom}
import ap.parser.SimpleClausifier

import scala.collection.mutable.{Stack, ArrayBuffer, ListBuffer}

object ConnectionProver {
  private val AC = Debug.AC_CONNECTION_PROVER
}


class ConnectionProver(depthFirst : Boolean, preSettings : GoalSettings) {

  def orderToMap(order : BREUOrder) = {
      val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
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


  class ConnectionBranch(val nodes : List[Node], val closer : Closer, step : Int, val order : BREUOrder) {

    override def toString = {
      closer match {
        case Open => 
          "||\t(" + step + ") " + nodes.mkString(", ")
        case CloserPair(n1, n2) => 
          "||\t(" + step + ") " + nodes.mkString(", ") + " closed using " + (n1, n2)
        case CloserNegEq(n) => 
          "||\t(" + step + ") " + nodes.mkString(", ") + " closed using inequality (" + nodes(n) + ")"
      }
    }

    def isOpen = {
      closer match {
        case Open => true
        case _ => false
      }
    }

    def close(newCloser : Closer, newStep : Int) = {
      new ConnectionBranch(nodes, newCloser, newStep, order)
    }

    // TODO: Extra order, yuck...
    def extend(newOrderNode : OrderNode, extraOrder : BREUOrder) = {
      val (newNodes, newOrder) = newOrderNode
      val mergeOrder = order ++ extraOrder ++ newOrder
      new ConnectionBranch(newNodes ++ nodes, closer, step, mergeOrder)
    }

    def depth = (for (n <- nodes if isLiteral(n)) yield 1).sum


    def length = nodes.length

    def apply(idx : Int) = {
      nodes(idx)
    }


    // DONE
    def extractEquations : List[Equation] = {
      
      def extractEquationsAux(nodes : List[Node]) : List[Equation] = {
        if (nodes.isEmpty)
          List()
        else
          nodes.head match {
            case Equation(lhs, rhs) => Equation(lhs, rhs) :: extractEquationsAux(nodes.tail)
            case _ => extractEquationsAux(nodes.tail)
          }
      }
      extractEquationsAux(nodes)
    }

    def extractFunEquations : List[FunEquation] = {
      def extractFunEquationsAux(nodes : List[Node]) : List[FunEquation] = {
        if (nodes.isEmpty)
          List()
        else
          nodes.head match {
            case FunEquation(eq) => FunEquation(eq) :: extractFunEquationsAux(nodes.tail)
            case _ => extractFunEquationsAux(nodes.tail)
          }
      }
      extractFunEquationsAux(nodes)
    }

    def extractNegEquations : List[NegEquation] = {
      def extractNegEquationsAux(nodes : List[Node]) : List[NegEquation] = {
        if (nodes.isEmpty)
          List()
        else
          nodes.head match {
            case NegEquation(t1, t2) => NegEquation(t1, t2) :: extractNegEquationsAux(nodes.tail)
            case _ => extractNegEquationsAux(nodes.tail)
          }
      }
      extractNegEquationsAux(nodes)
    }

    def extractNegFunEquations : List[NegFunEquation] = {
      def extractNegFunEquationsAux(nodes : List[Node]) : List[NegFunEquation] = {
        if (nodes.isEmpty)
          List()
        else
          nodes.head match {
            case NegFunEquation(eq) => NegFunEquation(eq) :: extractNegFunEquationsAux(nodes.tail)
            case _ => extractNegFunEquationsAux(nodes.tail)
          }
      }
      extractNegFunEquationsAux(nodes)
    }


    // DONE
    def extractLiterals : List[Literal] = {
      def extractLiteralsAux(nodes : List[Node]) : List[Literal] = {
        if (nodes.isEmpty)
          List()
        else
          nodes.head match {
            case Literal(f) => Literal(f) :: extractLiteralsAux(nodes.tail)
            case _ => extractLiteralsAux(nodes.tail)
          }
      }
      extractLiteralsAux(nodes)
    }

    // DONE!
    // Checks whether the branch can be closed structurally
    // (i.e., contains predicates of opposite polarity or inequalites)
    def structuralClosable : Boolean = {
      closer match {
        case Open =>  false
        case CloserPair(cp1, cp2) => {
          val node1 = nodes(cp1)
          val node2 = nodes(cp2)
            (node1, node2) match {
            case (lit1 : Literal, lit2 : Literal) => structuralUnifiable(lit1, lit2)
            case _ => false
          }
        }
        case CloserNegEq(n) => {
          nodes.head match {
            case NegEquation(_, _) => true
            case _ => false
          }
        }
      }
    }
  }

  // TODO branches should probably be private
  class ConnectionTable(val branches : Seq[ConnectionBranch]) {

    override def toString =  branches.mkString("\n")
    def width = branches.length

    // Extend branch branchIdx with clause(idx) and add new branches to the right
    def extendBranch(branchIdx : Int, orderClause : OrderClause, idx : Int, newOrder : BREUOrder) = {
      val preBranches = branches.take(branchIdx)
      val postBranches = branches.drop(branchIdx + 1)
      val newBranches = for (c <- orderClause) yield branches(branchIdx).extend(c, newOrder)
      new ConnectionTable(preBranches ++ (newBranches(idx) :: newBranches.filter(_ != newBranches(idx)))  ++ postBranches)
    }

    def close(idx : Int, closer : Closer, step : Int) = {
      val newBranches = 
        for (i <- 0 until branches.length) yield {
          if (i == idx) {
            branches(i).close(closer, step)
          } else {
            branches(i)
          }
        }
      new ConnectionTable(newBranches)
    }


    def unifyBranches(selected : List[Int]) 
        : (Boolean, Option[Map[ConstantTerm, ConstantTerm]]) = {
      println("unifyBranches(" + selected.mkString(", "))
      val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](
        () => Timeout.check, 
        Param.CLAUSIFIER_TIMEOUT(preSettings))

      val problem = branchToBreu(selected, ccuSolver)

      println("problem: " + problem)

      val result = problem.solve
      if (result == ccu.Result.SAT)
        (true, Some(problem.getModel))
      else
        (false, None)
    }

    def unifyBranches() 
        : (Boolean, Option[Map[ConstantTerm, ConstantTerm]]) = 
      unifyBranches((0 until branches.length).toList)

    def closable(selected : List[Int]) : Boolean = {
      println("Closable(" + selected.mkString(", ") + ")")
      for (i <- selected)
        if (!branches(i).structuralClosable)
          return false

      println("\tStructural closable!")

      val (closed, _) = unifyBranches(selected)
      if (closed)
        println("\tUnifiable!")
      else
        println("\tNot closable")
      closed
    }

    def firstOpen = {
      val first = branches.find(_.isOpen)
      val idx = if (!first.isEmpty) (branches indexOf first.get) else -1
      (first, idx)
    }

    def branchToBreu(selected : List[Int], solver : ccu.CCUSolver[ConstantTerm, Predicate]) 
        : ccu.CCUInstance[ConstantTerm, Predicate] = {
      val res = branchToBreuAux(selected, solver)
      // println("<---branchToBreu--->")
      // for (b <- branches)
      //   println("\t" + b + "\n" + "  >>>")
      // println("   ----   ")
      // println(res)
      res
    }

    def branchToBreu(solver : ccu.CCUSolver[ConstantTerm, Predicate]) 
        : ccu.CCUInstance[ConstantTerm, Predicate] =
      branchToBreu((0 to branches.length).toList, solver)

    def branchToBreuAux(selected : List[Int], ccuSolver : ccu.CCUSolver[ConstantTerm, Predicate])
        : ccu.CCUInstance[ConstantTerm, Predicate]  = {
      // We need to keep track of domains
      val domains = combineOrders(for (s <- selected) yield branches(s).order)

      val subProblems =
        for (i <- selected) yield {
          val branch = branches(i)
          if (!branch.structuralClosable) {
            throw new Exception("Trying to create BREU-problem from structural open branch!")
          } else {
            val nodes = branch.nodes
            val closer = branch.closer

            val funEqs = branch.extractFunEquations.map(convertFunEquation(_))
            val eqs = branch.extractEquations.map(convertEquation(_)).flatten
            val negFunEqs = branch.extractNegFunEquations.map(convertNegFunEquation(_))

            // println("BRANCH: " + branch)
            // println("\tfunEqs: " + funEqs)
            // println("\teqs: " + eqs)
            // println("\tnegFunEqs: " + negFunEqs)

            val argGoals : List[(ConstantTerm, ConstantTerm)] =
              closer match {
                case (CloserPair(n1, n2)) => {
                  // TODO: How do we order
                  (nodes(n1), nodes(n2)) match {
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
                    case _ => throw new Exception("Closer Pair is pointing wrong!")
                  }
                }
                case CloserNegEq(n) => {
                  (nodes(n)) match {
                    case (NegEquation(t1, t2)) => {
                      List((t1, t2))
                    }
                    case _ => throw new Exception("Closer NegEq is pointing wrong!")
                  }
                }
                case _ => throw new Exception("Implement: argGoals for Negeqs!")
              }
            (List(argGoals.toList), funEqs ++ eqs, negFunEqs)
          }
        }
      ccuSolver.createProblem(domains.toMap, subProblems.map(_._1), subProblems.map(_._2), subProblems.map(_._3))
    }
  }


  // A branch is its list of formulas, an optional pair of nodes
  // closing the branch and a number describing what steps have been
  // tried .The steps are in range
  // [0 .. branch.length - 1 .. branch.length - 1 + |Input Clauses*Clause length|].
  // I.e., first we try the nodes on the branch, then the input clauses.
  abstract class Node
  case class Literal(formula : PredConj) extends Node
  case class FunEquation(eq : PredConj) extends Node
  case class NegFunEquation(eq : PredConj) extends Node
  case class Equation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node
  case class NegEquation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node

  def isLiteral(n : Node) = {
    n match {
      case Literal(_) => true
      case _ => false
    }
  }

  def isEquation(n : Node) = {
    !isLiteral(n)
  }

  abstract class Closer
  case class CloserPair(node1 : Int, node2 : Int) extends Closer
  case class  CloserNegEq(node : Int) extends Closer
  case object Open extends Closer

  // TODO: How to make this nicer?
  var nextPredicate = 0
  var nextTerm = 0


  // A term in a BREUOrder which is (_, false) is a constant while
  // (_, true) is a variable which can take the value of any variable or
  // constant earlier in the order.
  type BREUOrder = List[(ConstantTerm, Boolean)]
    // We use a special kind of clause where each literal can actually be a list of literals (to allow equations)
  type Clause = List[List[Node]]
  type OrderNode = (List[Node], BREUOrder)
  type OrderClause = List[OrderNode]

  def clauseToString(clause : OrderClause) : String = 
    (for ((nodes, _) <- clause) yield {
      nodes.mkString("^") + ")"
      }).mkString(" v ")


  // Convert a conjunction to a list of clauses (with each node being a formula followed by assumptions)
  // DONE!
  def convertConjunction(conj : Conjunction) = {
    val singlePredicates = for (p <- conj.predConj.iterator) yield (p, List())
    val predicatesWithFacts =
      for (pwf <- conj.negatedConjs) yield {
        val assumptions = ListBuffer() : ListBuffer[PredConj]
        val formulas = ListBuffer() : ListBuffer[PredConj]

        for (p <- pwf.predConj.iterator) {
          if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
            assumptions += p
          } else if (p.predicates.size == 1) {
            formulas += !p
          } else {
            throw new Exception("More than one predicate in predConj!")
          }
        }

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, formulas.length == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////

        (formulas.head, assumptions.toList)
      }

    (singlePredicates ++ predicatesWithFacts).toList
  }

  // Instantiate first level conj with new variables added to order with prefix
  // DONE
  def inst(conj : Conjunction, prefix : String, order : TermOrder) : (Conjunction, BREUOrder, TermOrder) = {
    var allCount = -1
    var exCount = -1

    val quants =
      for (q <- conj.quans) yield {
        q match {
          case Quantifier.ALL => {
            allCount += 1
            (new ConstantTerm(prefix + "ALL" + allCount), true)
          }
          case Quantifier.EX => {
            exCount += 1
            (new ConstantTerm(prefix + "EX" + exCount), false)
          }
        }
      }

    val newOrder = conj.order.extend(quants.map(_._1))
    (conj.instantiate(quants.map(_._1))(newOrder), quants.toList, newOrder)
  }


  // Fully instantiate conj with prefix
  // DONE
  def fullInst(conj : Conjunction, prefix : String) = {
    // Instantiate top-level
    val allTerms : ListBuffer[(ConstantTerm, Boolean)] = ListBuffer()

    val (newConj, nt, norder) = inst(conj, prefix, conj.order)
    allTerms ++= nt


    val retVal =
      if (newConj.negatedConjs.size == 1) {
        val disjunction = newConj.negatedConjs(0)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, disjunction.quans.length == 0)
        //-END-ASSERTION-//////////////////////////////////////////////////////////

        // Check all assumption-based formulas:
        var negOrder = norder
        val updatedNegConj =
          for (nc <- disjunction.negatedConjs) yield {
            val (newConj, nt, tmporder) = inst(nc, prefix + "_disj", negOrder)
            negOrder = tmporder
            allTerms ++= nt
            newConj
          }

        val tmp = disjunction.negatedConjs.update(updatedNegConj, negOrder)
        val finalDisjunction = disjunction.updateNegatedConjs(tmp)(negOrder)
        val tmp2 = newConj.negatedConjs.update(List(finalDisjunction), negOrder)
        val finalConj = newConj.updateNegatedConjs(tmp2)(negOrder)
        (finalConj, allTerms.toList, negOrder)
      } else {
        (newConj, allTerms.toList, norder)
      }

    // println("fullInst(" + conj + ") => " + retVal)
    retVal
  }



  // Converts a pc representing a conjunction to a triple
  // DONE!
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

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  // DONE
  // def checkUnifiability(lit1 : Literal, lit2 : Literal, equations : List[FunEquation], order : BREUOrder) : Boolean = {
  //   val (pred1, pred2) = (lit1.formula, lit2.formula)

  //   val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](() => Timeout.check, Param.CLAUSIFIER_TIMEOUT(preSettings))
    
  //   // We need to keep track of domains
  //   val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
  //   for ((t, uni) <- order.reverse) {
  //     domain += (t -> Set(t))
  //     if (uni) {
  //       for (k <- domain.keys) {
  //         domain += (t -> (domain(t) + k))
  //       }
  //     }
  //   }

  //   // println("order: " + order)
  //   // println("domain: "+  domain)

  //   //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //   Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
  //   //-END-ASSERTION-//////////////////////////////////////////////////////////

  //   // Two cases, either pred1 and !pred2 or !pred1 and pred2
  //   if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
  //     (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
  //     return false
  //   }

  //   // println("\tNegation-compatible")

  //   // They have to share predicate symbol
  //   val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
  //   val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

  //   if (pred1atom.pred != pred2atom.pred)
  //     return false

  //   // println("\tPredicate-compatible")

  //   // Unify each argument
  //   val argGoals = 
  //     for ((arg1, arg2) <- pred1atom zip pred2atom) yield {
  //       //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  //       Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
  //       //-END-ASSERTION-//////////////////////////////////////////////////////////
  //       // println("\t" + arg1 + "\t?=\t" + arg2)
  //       (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
  //     }

  //   // Convert functions
  //   val eqs = 
  //     for (e <- equations) yield {
  //       convertEquation(e)
  //     }
  //   val problem = ccuSolver.createProblem(domain.toMap, List(List(argGoals)), List(eqs))
  //   val result =  problem.solve
  //   // println(result)
  //   if (result == ccu.Result.SAT) {
  //     // println(problem.getModel)
  //     true
  //   } else {
  //     false
  //   }
  // }

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  // DONE
  def structuralUnifiable(node1 : Literal, node2 : Literal) : Boolean = {
    (node1, node2) match {
      case (Literal(pred1), Literal(pred2)) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
        //-END-ASSERTION-//////////////////////////////////////////////////////////

        // Two cases, either pred1 and !pred2 or !pred1 and pred2
        if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
          (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
          return false
        }

        // println("\tNegation-compatible")
        // They have to share predicate symbol
        val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
        val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

        if (pred1atom.pred != pred2atom.pred)
          return false

        true
      }
      case _ => false
    }
  }









  // DONE
  def findStatement(inputClauses : List[Conjunction], step : Int) :
      (Conjunction, Int) = {
    if (step >= clauseWidth(inputClauses.head))
      findStatement(inputClauses.tail, step - clauseWidth(inputClauses.head))
    else
      (inputClauses.head, step)
  }

  var maxDepthReached = false
  var maxWidthReached = false

  def solveTable(
    table : ConnectionTable,
    inputClauses : List[Conjunction],
    maxDepth : Int,
    maxWidth : Int,
    iteration : Int) :
      Option[ConnectionTable] = {

    println("//-------------------------")
    println("|| Starting recursive iteration " + iteration)
    println("|| Branches: ")
    println(table)

    // println("|| Current terms:")
    // println("||\t" + terms)

    // Pick a branch -- Always pick first open branch
    // TODO: Any way of making branch a val and branchStep a var?
    val (extendingBranch, extendingBranchIdx) = table.firstOpen

    // If no open branch, we are done
    if (extendingBranch.isEmpty)
      return Some(table)

    var branch = extendingBranch.get
    val branchIdx = extendingBranchIdx
    val branchAtom = branch(0)

    println("|| Extending branch (" + branchIdx + "): ")
    println("||\t" + branch)

    // If branch is too long, stop
    if (branch.depth > maxDepth) {
      println("|| MAX DEPTH REACHED")
      maxDepthReached = true
      return None
    }

    if (table.width > maxWidth) {
      println("|| MAX WIDTH REACHED")
      maxWidthReached = true
      return None
    }

    def tryStep(step : Int) : Option[ConnectionTable] = {
      println("// -- Trying step: " + step)
      val closedTable = 
        if (step == 0) {
          val closedTable = table.close(branchIdx, CloserNegEq(0), step)
          closedTable
        } else if (step < branch.length) {
          // Try unifying with node on branch
          val closedTable = table.close(branchIdx, CloserPair(0, step), step)
          // val closingBranch = (branch, CloserPair(0, step), step)
          closedTable
        } else {
          // Try unifying with input clause, first we try first clause, first statement,
          // then first clause, second statement, ...
          val (clause, idx) = findStatement(inputClauses, step - branch.length)
          val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)

          // TODO: This should not be here, negatedConjs should probably be used somewhere else...
          val orderClause = conjToClause(instClause, false)
          val extendedTable = table.extendBranch(branchIdx, orderClause, idx, newOrder)

          val closingPair = CloserPair(0, orderClause(idx)._1.length)
          val closedTable = extendedTable.close(branchIdx, closingPair, step)
          closedTable
          // val allBranches = (for (s <- stmts) yield (s ++ branch).toList).toList

          // val closingBranch = (allBranches(idx), closingPair, step)
          // val otherBranches =
          //   (allBranches.take(idx) ++ allBranches.drop(idx + 1)).map((_, Open, 0))
          // (closingBranch, otherBranches, newOrder)
          
        }

      val selected = (0 to branchIdx).toList

      // println("Selected: " + selected.mkString(", "))
      // println("closedOrder: " + closedOrder)
      if (closedTable.closable(selected)) {
        println("Closable!\n----")
        Some(closedTable)
      } else {
        println("Not closable...\n---")
        None
      }
      // val checkOrder = (tmpOrder ++ terms).toList
      // val checkBranches =
      //   closeB :: (for (i <- 0 until table.length; if (i != branchIdx); if (!isOpen(table(i)))) yield table(i)).toList
      // lazy val (unifiable, model) = checkBranches.unifyBranches(checkOrder)


      // if (structuralClosable(closeB) && unifiable) {
      //   val newTable =
      //     (for (i <- 0 until branchIdx) yield table(i)) ++
      //   (closeB :: otherB) ++
      //   (for (i <- (branchIdx + 1) until table.length) yield table(i))
      //   Some((newTable.toList, checkOrder))
      // } else {
      //   None
      // }

    }

    // We use the branchStep to decide where to search for the new candidate
    // TODO: Once again, negatedConjs(0), also, -1?
    // val maxStep = branch.length + (inputClauses.map((x : Conjunction) => clauseWidth(x.negatedConjs(0))).sum) - 1
    val maxStep = branch.length + (inputClauses.map(clauseWidth(_)).sum)
    println("|| MaxStep: " + maxStep)
    // println("|| \t" + inputClauses)
    // println("|| \t" + inputClauses.map(clauseWidth(_)))
    var branchStep = 0


    // TODO: Should this be <=?
    while (branchStep < maxStep) {
      val res = tryStep(branchStep)
      if (!res.isEmpty) {
        // If actually closed branch, recurse!
        println("Applying step: " + branchStep)
        val (clause, idx) = findStatement(inputClauses, branchStep - branch.length)
        println("\t" + clause + " (" + idx + ")")
        val newTable = res.get
        val rec = solveTable(newTable, inputClauses, maxDepth, maxWidth, iteration + 1)
        if (!rec.isEmpty)
          return rec
      }
      branchStep += 1
    }
    println("|| No applicable formula found...")
    println("|| Couldn't close table: ")
    println(table)
    println("\n\n\n")
    None
  }

  def predToNodes(predConj : PredConj, negated : Boolean) : OrderClause = {
    // println("predToNodes(" + predConj + ", " + negated + ")")
    
    val newNodes = ListBuffer() : ListBuffer[OrderNode]

    for (p <- predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        if (negated) {
          // Convert to a funeq and a negeq
          val (_, _, res2) = convertNegFunEquation(NegFunEquation(p))
          // println("fun: " + fun)
          // println("args: " + args)
          // println("res: " + res)
          // funEqs += NegFunEquation(p)

          val pc = p
          val atom = pc.positiveLits(0)
          val fun = atom.pred
          val args = atom.take(atom.length-1)
          val res = atom(atom.length-1)
          val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
          val newOrder = List((newTerm, false))
          val no = p.order.extend(newTerm)

          nextTerm += 1
          val lc = LinearCombination(newTerm, no)
          val newFunEq = Atom(fun, args ++ List(lc), no)
          // println("Converting " + p + " to:")
          // println("\tnewFunEq: " + newFunEq)

          val newEq = NegEquation(res2, newTerm)
          // println("\tnewEq = " + newEq)	ALL (! (!R(_0) & ! EX (f(_1, _0) & R(_0)))) => List(List(Literal(R(convALL0))), List(FunEquation(f(convALL0, conv_disjEX0))), List(Literal(R(conv_disjEX0))))

          // TODO: Fix this!
          val asd1 : List[Node] = List(newEq, FunEquation(PredConj(List(newFunEq), List(), no)))
          val asd2 : BREUOrder = newOrder
          val asd3 : OrderNode = (asd1, asd2)
          newNodes += asd3

        } else {
          val asd1 = List(FunEquation(p)) : List[Node]
          val asd2 = List() : BREUOrder
          newNodes += ((asd1, asd2) )
        }
      } else if (p.predicates.size == 1) {
        if (negated)
          newNodes += ((List(Literal(!p)), List()))
        else
          newNodes += ((List(Literal(p)), List()))
      } else {
        throw new Exception("More than one predicate in predConj!")
      }
    }

    val finalNodes = 
      if (newNodes.isEmpty) {
        List()
      } else {
        // TODO: Not sure about this one
        if (negated) {
          newNodes.toList
        } else { 
          // TODO: Do we have to place the orders in some kind of order (no pun intended)
          val newEq : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if isEquation(n)) yield n
          val newLits : List[Node] = for (n <- newNodes.map(_._1).flatten.toList if isLiteral(n)) yield n
          val newOrder : BREUOrder = newNodes.map(_._2).flatten.toList
          List((newLits ++ newEq, newOrder))
        }
      }
    // println("\t" + finalNodes)
    finalNodes
  }

  // Can only be used on instatiated clauses!
  def arithToNodes(arithConj : ArithConj, negated : Boolean) : OrderClause = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, arithConj.inEqs.size == 0 && arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (arithConj.isTrue) { 
      List()
    } else {
      // println("arithToLiteral(" + arithConj + ")")
      val nodes : OrderClause =
        for (eq <- arithConj.negativeEqs.toList) yield {
          // println("\t" + eq)
          val pairs = eq.pairSeq.toList
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, pairs.length == 2)
          //-END-ASSERTION-//////////////////////////////////////////////////////////
          val (c1, t1) = pairs(0)
          val (c2, t2) = pairs(1)
          // println("\t\t" + (c1, t1) + " ... " + (c2, t2))
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, (c1.intValue == 1 && c2.intValue == -1) || (c1.intValue == -1 && c2.intValue == 1) )
          //-END-ASSERTION-//////////////////////////////////////////////////////////
          // println(arithConj + " => " + t1 + " != " + t2)
          // println("t1: " + t1 + " (" + t1.getClass + ")")
          // println("t2: " + t2 + " (" + t2.getClass + ")")
            (t1, t2) match {
            case (ct1 : ConstantTerm, ct2 : ConstantTerm) => 
              if (negated) 
                (List(Equation(ct1, ct2)), List()) : OrderNode
              else 
                (List(NegEquation(ct1, ct2)), List()) : OrderNode
            case _ => 
              throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
          }
        }
      nodes
    }
  }

  def conjToList(conj : Conjunction, negated : Boolean) : List[OrderNode] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    predLiterals ++ eqLiterals
  }


  def subConjToClause(conj : Conjunction, negated : Boolean) : List[OrderNode] = {
    // println("subConjToClause(" + conj + ", " + negated + ")")
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    val singleLiterals = (predLiterals ++ eqLiterals)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    // println("\tpredLiterals: " + predLiterals)
    // println("\teqLiterals: " + eqLiterals)
    // println("\tconj.negatedConjs: " + conj.negatedConjs)
    if (conj.negatedConjs.isEmpty) {
      // Only one literals
      singleLiterals
    } else {
      val negLiterals = conjToList(conj.negatedConjs.head, !negated)
      // println("\tnegLiterals: " + negLiterals)
      singleLiterals ++ negLiterals
    }
  }

  def conjToClause(conj : Conjunction, negated : Boolean) : OrderClause = {
    // println("conjToClause(" + conj + ", " + negated + ")")
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    // println("predConj: " + conj.predConj)
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    // println("\tpredLiterals: " + predLiterals)
    // println("\tarithLiters: " + eqLiterals)

    // The negative literals should be returned as one List of list of nodes
    val negLiterals =
      if (conj.negatedConjs.length == 0)
        List()
      else
        subConjToClause(conj.negatedConjs(0), !negated)



    // println("\tnegLiterals: " + negLiterals)

    // TODO: If a conj has both arith and pred (or several of one/both) is that one node or several?
    // val res: List[List[Node]] = 
    //   if (negLiterals.isEmpty)
    //     List(thisNode)
    //   else if (thisNode.isEmpty)
    //     negLiterals
    //   else
    //     thisNode :: negLiterals
    
    // Now we combine both the top-level literals as well as the multi-part literals
    val res : OrderClause = predLiterals ++ eqLiterals ++ negLiterals

    // println("conjToClause(" + conj + ", " + negated + ")")
    // println("\t" + res)
    res
  }

  def clauseWidth(conj : Conjunction) = conjToClause(fullInst(conj, "clauseWidth")._1, false).length

  def extractConstants(conjs : List[Conjunction]) : BREUOrder = {
    (for (c <- conjs) yield c.constants).toSet.flatten.toList.map((_, false))
  }

  def solve(givenFor : Conjunction, termOrder : TermOrder) = {
    // Since the formula is in CNF, everything should be in the negated conjunctions

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC, givenFor.predConj.size == 0 && givenFor.arithConj.isEmpty)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    println("\n\nSolving Table")
    val quans = givenFor.quans
    val tmpConstants = for (i <- 0 until givenFor.quans.length) yield (new ConstantTerm("CONSTANT_" + i))
    val tmpOrder = givenFor.order.extend(tmpConstants)
    val closedFor = givenFor.instantiate(tmpConstants)(tmpOrder)
    val negQuans = closedFor.negate.quans
    val inputClauses = closedFor.negate.iterator.toList.reverse

    println("Input Clauses (DEBUG)")
    for (c <- inputClauses) 
      println("\t" + c + " => " + (conjToClause(fullInst(c, "conv")._1, false)))

    val clauses = for (c <- inputClauses) yield { Conjunction.quantify(negQuans, c, c.order) }


    println("Input Clauses: ")
    for (c <- inputClauses) 
      println("\t" + clauseToString((conjToClause(fullInst(c, "conv")._1, false))))

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)

    def tryFirstClause(idx : Int, maxDepth : Int, maxWidth : Int) :
        (Option[ConnectionTable], Boolean, Boolean) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("\n\nTrying with inital clause: " + firstClause)

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)

      // TODO: initOrder2!?, come on ...
      val initTable  =
        new ConnectionTable(for ((nodes, extraOrder) <- conjToClause(firstClause, false)) yield {
          val initOrder2 = initOrder ++  extraOrder
          new ConnectionBranch(nodes, Open, 0, initOrder2)
        })



      maxDepthReached = false
      maxWidthReached = false
      val result = solveTable(initTable, clauses, maxDepth, maxWidth, 0)
      if (result.isEmpty) {
        println("Could not close table")
        (None, maxDepthReached, maxWidthReached)
      } else {
        val finalTable = result.get
        (Some(finalTable), false, false)
      }
    }


    var table = None : Option[ConnectionTable]

    var maxDepth = 6
    var maxWidth = 10
    var reachedMaxDepth = true
    var reachedMaxWidth = true

    while (table.isEmpty && (reachedMaxDepth || reachedMaxWidth)) {
      var tryIdx = 0
      reachedMaxDepth = false
      reachedMaxWidth = false
      println("//-----------------------------")
      println("||  TRYING maxDepth: " + maxDepth)
      println("||  TRYING maxWidth: " + maxWidth)
      println("||")
      println("||")
      while (table.isEmpty && tryIdx < clauses.length) {
        val (resTable, rMaxDepth, rMaxWidth) = tryFirstClause(tryIdx, maxDepth, maxWidth)
        table = resTable
        if (rMaxDepth)
          reachedMaxDepth = true
        if (rMaxWidth)
          reachedMaxWidth = true
        tryIdx += 1
      }

      println("Increasing depths:")
      if (reachedMaxDepth) {
        maxDepth *=2
        println("\tmaxDepth = " + maxDepth)
      }
      if (reachedMaxWidth) {
        maxWidth *=2
        println("\tmaxWidth = " + maxWidth)
      }
    }

    if (!table.isEmpty) {
      val finalTable = table.get
      val (unifiable, finalMap) = finalTable.unifyBranches()
      println("CLOSED TABLE:")
      // println("with order: " + finalOrder.mkString(", "))
      for (b <- finalTable.branches)
        println("\t" + b)
      println("Using: " + finalMap)
      (true, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    } else {
      println("Could not close table")
      (false, Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings))
    }
  }
}
