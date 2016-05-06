//
// Todo:
// Fix ArithConj! How do we use these?
//
// We have to use CloserPair in some cases but other times we use CloseEnd!
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

  // A branch is its list of formulas, an optional pair of nodes
  // closing the branch and a number describing what steps have been
  // tried .The steps are in range 
  // [0 .. branch.length - 1 .. branch.length - 1 + |Input Clauses*Clause length|]. 
  // I.e., first we try the nodes on the branch, then the input clauses.
  abstract class Node
  case class Literal(formula : PredConj) extends Node
  case class FunEquation(eq : PredConj) extends Node
  case class NegEquation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node

  abstract class Closer
  case class CloserPair(node1 : Int, node2 : Int) extends Closer
  case class  CloserNegEq(node : Int) extends Closer
  case object Open extends Closer


  type Branch = (List[Node], Closer, Int)
  type Table = List[Branch]

  // Branch isOpen
  // TODO: Make Branch a class?
  def isOpen(branch : Branch) = {
    val (_, closer, _) = branch
    closer match {
      case Open => true
      case _ => false
    }
  }




  // A term in a BREUOrder which is (_, false) is a constant while
  // (_, true) is a variable which can take the value of any variable or
  // constant earlier in the order.
  type BREUOrder = List[(ConstantTerm, Boolean)]

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

  // DONE
  def unifyBranches(branches : List[Branch], order : BREUOrder) : (Boolean, Option[Map[ConstantTerm, ConstantTerm]]) = {
    val problems = for (b <- branches) yield branchToBreu(b, order)

    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](() => Timeout.check, Param.CLAUSIFIER_TIMEOUT(preSettings))
    val domains = problems.head.get._1
    // TODO: Should we really do .head here?
    val argGoals = problems.map(_.get._2.head)
    val eqs = problems.map(_.get._3.head)
    val problem = ccuSolver.createProblem(domains, argGoals, eqs)
    val result =  problem.solve
    if (result == ccu.Result.SAT)
      (true, Some(problem.getModel))
    else
      (false, None)
  }

  // Converts a pc representing a conjunction to a triple
  // DONE!
  def convertEquation(funEq : FunEquation) = {
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

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  // DONE
  def checkUnifiability(lit1 : Literal, lit2 : Literal, equations : List[FunEquation], order : BREUOrder) : Boolean = {
    val (pred1, pred2) = (lit1.formula, lit2.formula)

    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](() => Timeout.check, Param.CLAUSIFIER_TIMEOUT(preSettings))
    
    // We need to keep track of domains
    val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
    for ((t, uni) <- order.reverse) {
      domain += (t -> Set(t))
      if (uni) {
        for (k <- domain.keys) {
          domain += (t -> (domain(t) + k))
        }
      }
    }

    // println("order: " + order)
    // println("domain: "+  domain)

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

    // println("\tPredicate-compatible")

    // Unify each argument
    val argGoals = 
      for ((arg1, arg2) <- pred1atom zip pred2atom) yield {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        // println("\t" + arg1 + "\t?=\t" + arg2)
        (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
      }

    // Convert functions
    val eqs = 
      for (e <- equations) yield {
        convertEquation(e)
      }
    val problem = ccuSolver.createProblem(domain.toMap, List(List(argGoals)), List(eqs))
    val result =  problem.solve
    // println(result)
    if (result == ccu.Result.SAT) {
      // println(problem.getModel)
      true
    } else {
      false
    }
  }

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


  // DONE!
  // Checks whether the branch can be closed structurally
  // (i.e., contains predicates of opposite polarity or inequalites)
  def structuralClosable(branch : Branch) : Boolean = {
    val (b, cp, step) = branch
    cp match {
      case Open =>  false
      case CloserPair(cp1, cp2) => {
        val node1 = b(cp1)
        val node2 = b(cp2)
        (node1, node2) match {
          case (lit1 : Literal, lit2 : Literal) => structuralUnifiable(lit1, lit2)
          case _ => false
        }
      }
      case CloserNegEq(n) => {
        b.head match {
          case NegEquation(_, _) => true
          case _ => false
        }
      }
    }
  }


  def branchToBreu(branch : Branch, order : BREUOrder) = {
    val res = branchToBreuAux(branch, order)
    // println("<---branchToBreu--->")
    // println(branch)
    // println("   ----   ")
    // if (res.isEmpty)
    //   println("NONE")
    // else {
    //   val (a, b, c) = res.get
    //   println(a)
    //   println("---")
    //   println(b)
    //   println("---")
    //   println(c)
    //   println("$$$$")
    // }
    res
  }

  def branchToBreuAux(branch : Branch, order : BREUOrder) : 
      Option[(Map[ConstantTerm,Set[ConstantTerm]], List[List[List[(ConstantTerm, ConstantTerm)]]], List[List[(Predicate, List[ConstantTerm], ConstantTerm)]])] = {

    // We need to keep track of domains
    val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
    for ((t, uni) <- order.reverse) {
      domain += (t -> Set(t))
      if (uni) {
        for (k <- domain.keys) {
          domain += (t -> (domain(t) + k))
        }
      }
    }

    if (!structuralClosable(branch)) {
      None
    } else {
      val (nodes, closer, _) = branch

      val eqs = extractEquations(branch).map(convertEquation(_))

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
      Some((domain.toMap, List(List(argGoals.toList)), List(eqs)))
    }
  }

  // DONE
  def extractEquations(branch : Branch) : List[FunEquation] = {
    def extractEquationsAux(nodes : List[Node]) : List[FunEquation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case FunEquation(eq) => FunEquation(eq) :: extractEquationsAux(nodes.tail)
          case _ => extractEquationsAux(nodes.tail)
        }
    }
    extractEquationsAux(branch._1)
  }

  def extractNegEquations(branch : Branch) : List[NegEquation] = {
    def extractNegEquationsAux(nodes : List[Node]) : List[NegEquation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case NegEquation(t1, t2) => NegEquation(t1, t2) :: extractNegEquationsAux(nodes.tail)
          case _ => extractNegEquationsAux(nodes.tail)
        }
    }
    extractNegEquationsAux(branch._1)
  }


  // DONE
  def extractLiterals(branch : Branch) : List[Literal] = {
    def extractLiteralsAux(nodes : List[Node]) : List[Literal] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case Literal(f) => Literal(f) :: extractLiteralsAux(nodes.tail)
          case _ => extractLiteralsAux(nodes.tail)
        }
    }
    extractLiteralsAux(branch._1)
  }


  // DONE
  def findStatement(inputClauses : List[Conjunction], step : Int) :
      (Conjunction, Int) = {
    if (step >= clauseWidth(inputClauses.head))
      findStatement(inputClauses.tail, step - clauseWidth(inputClauses.head))
    else
      (inputClauses.head, step)
  }

  def solveTable(
    table : Table,
    terms : BREUOrder,
    inputClauses : List[Conjunction],
    maxDepth : Int,
    maxWidth : Int,
    iteration : Int) :
      Option[(List[Branch], BREUOrder)] = {

    println("//-------------------------")
    println("|| Starting recursive iteration " + iteration)
    println("|| Branches: ")
    for ((nodes, closer, step) <- table) {
      closer match {
        case Open => println("||\t(" + step + ") " + nodes.mkString(", "))
        case CloserPair(n1, n2) => println("||\t(" + step + ") " + nodes.mkString(", ") + " closed using " + (n1, n2))
        case CloserNegEq(n) => println("||\t(" + step + ") " + nodes.mkString(", ") + " closed using inequality (" + nodes(n) + ")")
      }
    }
    // println("|| Current terms:")
    // println("||\t" + terms)

    // Pick a branch -- Always pick first open branch
    // TODO: Any way of making branch a val and branchStep a var?
    val extendingBranch = table.find(x => x._2 match { case Open => { true } case _ => { false }})
    if (extendingBranch.isEmpty)
      return Some((table, terms))

    var (branch, _, _) = extendingBranch.get
    val branchIdx = table.indexOf(extendingBranch.get)
    val branchAtom = branch(0)
    val branchEqs = extractEquations(extendingBranch.get)

    println("|| Extending branch (" + branchIdx + "): ")
    println("||\t" + branch)

    // If branch is too long, stop
    if (branch.length >= maxDepth) {
      println("|| MAX DEPTH REACHED")
      return None
    }

    if (table.length >= maxWidth) {
      println("|| MAX WIDTH REACHED")
      return None
    }

    def tryStep(step : Int) = {
      val (closeB, otherB, tmpOrder) : (Branch, List[Branch], BREUOrder) =
        if (step == 0) {
          val closingBranch = (branch, CloserNegEq(0), step)
          (closingBranch, List(), List())
        } else if (step < branch.length) {
          // Try unifying with node on branch
          val closingBranch = (branch, CloserPair(0, step), step)
          (closingBranch, List(), List())
        } else {
          // Try unifying with input clause, first we try first clause, first statement,
          // then first clause, second statement, ...
          val (clause, idx) = findStatement(inputClauses, step - branch.length)
          val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
          // TODO: This should not be here, negatedConjs should probably be used somewhere else...
          val stmts = conjToClause(instClause, false)
          val allBranches = (for (s <- stmts) yield (s ++ branch).toList).toList
          val closingPair = CloserPair(0, stmts(idx).length)
          val closingBranch = (allBranches(idx), closingPair, step)
          val otherBranches =  
            (allBranches.take(idx) ++ allBranches.drop(idx + 1)).map((_, Open, 0))
          (closingBranch, otherBranches, newOrder)
        }

      val checkOrder = (tmpOrder ++ terms).toList
      val checkBranches =
        closeB :: (for (i <- 0 until table.length; if (i != branchIdx); if (!isOpen(table(i)))) yield table(i)).toList
      lazy val (unifiable, model) = unifyBranches(checkBranches, checkOrder)
      if (structuralClosable(closeB) && unifiable) {
        val newTable =
          (for (i <- 0 until branchIdx) yield table(i)) ++
        (closeB :: otherB) ++
        (for (i <- (branchIdx + 1) until table.length) yield table(i))
        Some((newTable.toList, checkOrder))
      } else {
        None
      }
    }

    // def candidateStep(step : Int) = {
    //   val closeB =
    //     if (step < branch.length) {
    //       // Try unifying with node on branch
    //       val closingBranch = (branch, Some(0, step), step)
    //       (closingBranch)
    //     } else {
    //       // Try unifying with input clause, first we try first clause, first statement,
    //       // then first clause, second statement, ...
    //       val (clause, idx) = findStatement(inputClauses, step - branch.length)
    //       val (instClause, newOrder, _) = fullInst(clause, "branch_" + iteration)
    //       // TODO: This should not be here, negatedConjs should probably be used somewhere else...
    //       // val stmts = newConvertConjunction(instClause.negatedConjs(0))
    //       val stmts = conjToClause(instClause, false)
    //       val allBranches = (for (i <- 0 until stmts.length) yield (stmts(i)._1 :: stmts(i)._2 ++ branch).toList).toList
    //       // Close this node with node above (ignoring the added equations)
    //       // TODO: Here we have a bug
    //       val closingPair = Some((0, 1 + stmts(idx)._2.length))
    //       val closingBranch = (allBranches(idx), closingPair, step)
    //       closingBranch
    //     }

    //   structuralClosable(closeB)
    // }

    // We use the branchStep to decide where to search for the new candidate
    // TODO: Once again, negatedConjs(0), also, -1?
    // val maxStep = branch.length + (inputClauses.map((x : Conjunction) => clauseWidth(x.negatedConjs(0))).sum) - 1
    val maxStep = branch.length + (inputClauses.map(clauseWidth(_)).sum)
    println("|| MaxStep: " + maxStep)
    // println("|| \t" + inputClauses)
    // println("|| \t" + inputClauses.map(clauseWidth(_)))
    var branchStep = 0


    // val candidateSteps =
    //   for (i <- 0 until maxStep; if candidateStep(i)) yield i
    // println("|| Candidate Steps: " + candidateSteps)

    // TODO: Should this be <=
    // TODO: We can check only candidate steps instead (or just stop the candidate steps)
    while (branchStep < maxStep) {
      // Try this step
      val res = tryStep(branchStep)
      if (!res.isEmpty) {
        // If actualy closed branch, recurse!
        println("Applying step: " + branchStep)
        val (clause, idx) = findStatement(inputClauses, branchStep - branch.length)
        println("\t" + clause + " (" + idx + ")")
        val (newTable, newOrder) = res.get
        val rec = solveTable(newTable, newOrder, inputClauses, maxDepth, maxWidth, iteration + 1)
        if (!rec.isEmpty) {
          println("Success(" + branchStep + ")")
          return rec
        } else {
          println("Fail(" + branchStep + ")")
        }
      }
      branchStep += 1
    }
    None
  }



  def predToNodes(predConj : PredConj, negated : Boolean) : List[Node] = {
    val funEqs = ListBuffer() : ListBuffer[Node]
    val literals = ListBuffer() : ListBuffer[Node]

    for (p <- predConj.iterator) {
      if ((p.predicates.size == 1) && (p.predicates subsetOf Param.FUNCTIONAL_PREDICATES(preSettings))) {
        funEqs += FunEquation(p)
      } else if (p.predicates.size == 1) {
        if (negated)
          literals += Literal(!p)
        else
          literals += Literal(p)
      } else {
        throw new Exception("More than one predicate in predConj!")
      }
    }

    literals.toList ++ funEqs.toList
  }

  // Can only be used on instatiated clauses!
  def arithToNodes(arithConj : ArithConj, negated : Boolean) : List[Node] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, arithConj.inEqs.size == 0 && arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (arithConj.isTrue) { 
      List()
    } else {
      // println("arithToLiteral(" + arithConj + ")")
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
          case (ct1 : ConstantTerm, ct2 : ConstantTerm) => NegEquation(ct1, ct2)
          case _ => throw new Exception("Non ConstantTerm in arithConj.negativeEqs (" + t1 + " : " + t1.getClass + ") (" + t2 + " : " + t2.getClass + ")")
        }
      }
    }
  }

  def conjToList(conj : Conjunction, negated : Boolean) : List[Node] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    predLiterals ++ eqLiterals
  }


  def subConjToClause(conj : Conjunction, negated : Boolean) : List[List[Node]] = {
    // println("subConjToClause(" + conj + ", " + negated + ")")
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    val singleLiterals = (predLiterals ++ eqLiterals).map(List(_))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (conj.negatedConjs.isEmpty) {
      // Only one literals
      singleLiterals
    } else {
      val negLiterals = conjToList(conj.negatedConjs.head, !negated)
      negLiterals :: singleLiterals
    }
  }

  def conjToClause(conj : Conjunction, negated : Boolean) : List[List[Node]] = {
    // println("conjToClause(" + conj + ", " + negated + ")")
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0 || conj.negatedConjs.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val predLiterals = predToNodes(conj.predConj, negated)
    val eqLiterals = arithToNodes(conj.arithConj, negated)
    // println("\tpredLiterals: " + conj.predConj)
    // println("\tarithLiters: " + conj.arithConj)
    // println("\tnegLiterals: " + conj.negatedConjs)


    // TODO: Is this correct?
    val thisNode = predLiterals ++ eqLiterals

    val negLiterals =
      if (conj.negatedConjs.length == 0)
        List()
      else
        subConjToClause(conj.negatedConjs(0), !negated)

    val res: List[List[Node]] = 
      if (negLiterals.isEmpty)
        List(thisNode)
      else if (thisNode.isEmpty)
        negLiterals
      else
        thisNode :: negLiterals

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
    println("givenFor: " + givenFor)
    val quans = givenFor.quans
    val tmpConstants = for (i <- 0 until givenFor.quans.length) yield (new ConstantTerm("CONSTANT_" + i))
    val tmpOrder = givenFor.order.extend(tmpConstants)
    val closedFor = givenFor.instantiate(tmpConstants)(tmpOrder)

    println("closedFor: " + closedFor)

    println("negate.quans: " + closedFor.negate.quans)
    val negQuans = closedFor.negate.quans
    val inputClauses = closedFor.negate.iterator.toList.reverse

    println("Input Clauses (before conversion)")
    for (c <- inputClauses) // 
      println("\t" + c)

    println("Input Clauses (after conversion)")
    for (c <- inputClauses) // 
      println("\t" + c + " => " + (conjToClause(fullInst(c, "conv")._1, false)))

    val clauses = 
      for (c <- inputClauses) yield {
        // println("\nOriginal clause: " + c)
        // println("\t" + c.quans)

        // println("Creating New clause")

        val newC = Conjunction.quantify(negQuans, c, c.order)
        // println("New clause: " + newC)
        // println("\t" + newC.quans)
        newC
      }

    val baseOrder = extractConstants(clauses) ++ List((new ConstantTerm("MIN"), false))
    println("Base Order: " + baseOrder)

    var maxDepth = 10
    var maxWidth = 10

    def tryFirstClause(idx : Int) = {

      val (firstClause, terms, newOrder) = fullInst(clauses(idx), "base")

      println("\n\nTrying with inital clause: " + firstClause)

      val initTable  =
        for (nodes <- conjToClause(firstClause, false)) yield {
          (nodes, Open, 0) : Branch
        }

      // We have to extract all terms in the problem
      val initOrder = (terms ++ baseOrder)

      val result = solveTable(initTable, initOrder, clauses, maxDepth, maxWidth, 0)
      if (result.isEmpty) {
        println("Could not close table")
        None
      } else {
        val (finalTable, finalOrder) = result.get
        // println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        // println("Final Order: " + finalOrder)
        // println("---------------------------")
        // println("Final Table:")
        // for (b <- finalTable)
        //   println("\t" + b)
        Some(finalTable, finalOrder)
      }
    }


    var table = None : Option[(Table, BREUOrder)]
    var tryIdx = 0
    while (table.isEmpty && tryIdx < clauses.length) {
      table = tryFirstClause(tryIdx)
      tryIdx += 1
    }

    if (!table.isEmpty) {
      val (finalTable, finalOrder) = table.get
      val (unifiable, finalMap) = unifyBranches(finalTable, finalOrder)
      println("CLOSED TABLE:")
      for (b <- finalTable)
        println("\t" + b)
      println("Using: " + finalMap)
    } else {
      println("Could not close table")
    }

    Goal(List(closedFor), Set(), Vocabulary(termOrder), preSettings)
  }
}
