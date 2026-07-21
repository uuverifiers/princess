/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.basetypes.IdealInt
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.types.{Sort, MonoSortedIFunction}
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal

import scala.collection.mutable.ArrayBuffer

object AllDifferent extends App {
  
  type TermTuple =     (IdealInt,      // Class
                        IdealInt,      // Lower bound
                        IdealInt)      // Upper bound
  type ValueBlock =    (Set[Int],      // Indexes
                        IdealInt,      // Lower bound
                        IdealInt)      // Upper bound

  /*
  type TermTable = IndexedSeq[TermTuple]

  val terms : TermTable =
    Vector((4, 0, 2), (0, 0, 5), (1, 1, 2), (2, 0, 1), (3, 0, 1))
  val terms2 : TermTable =
    for (n <- 0 until 100)
    yield (IdealInt(n), IdealInt(n), IdealInt(n))
  val terms3 : TermTable =
    for (n <- 0 until 10)
    yield (IdealInt(n), IdealInt(5), IdealInt(10))

  val rand = new scala.util.Random

  val terms4 : TermTable =
    for (n <- 0 until 1000;
         lb = rand.nextInt(100); ub = rand.nextInt(100);
         if lb <= ub)
    yield (IdealInt(rand.nextInt(100)), IdealInt(lb), IdealInt(ub))

  println(terms4)
*/

  abstract sealed class ConflictResult
  case class NoConflict(completeBlocks : Seq[ValueBlock])
    extends ConflictResult
  case class Conflict  (indexes : Seq[Int])
    extends ConflictResult

  def findConflicts(terms : Seq[TermTuple]) : ConflictResult = {
    val blocks = new ArrayBuffer[ValueBlock]
    findConflicts(terms.toList.zipWithIndex, List(), Set(), List(), blocks,
                  1, 0) match {
      case None          => NoConflict(blocks.toSeq)
      case Some(indexes) => Conflict(indexes)
    }
  }

  def findConflicts(terms            : List[(TermTuple, Int)],
                    selectedTerms    : List[Int],
                    coveredClasses   : Set[IdealInt],
                    blockedIntervals : List[(IdealInt, IdealInt)],
                    completeBlocks   : ArrayBuffer[ValueBlock],
                    lowerBound       : IdealInt,
                    upperBound       : IdealInt)
                                     : Option[List[Int]] =
    if (lowerBound + (selectedTerms.size + terms.size - 1) < upperBound) {
      // not possible to get a conflict or complete block, too few terms
      None
    } else {
      terms match {
        case List() => {
          None
        }
        case ((cl, _, _), index) :: otherTerms if coveredClasses(cl) => {
          // only include one term per class
          findConflicts(otherTerms, selectedTerms, coveredClasses,
                        blockedIntervals, completeBlocks,
                        lowerBound, upperBound)
        }
        case ((cl, lb, ub), index) :: otherTerms => {
          assert(selectedTerms.isEmpty ||
                 !(lowerBound <= lb && ub <= upperBound));
          {
            // Case 1: skip this term
            // remember that we chose to not use this term, block the interval
            val newBlockedIntervals = (lb, ub) :: blockedIntervals
            findConflicts(otherTerms, selectedTerms, coveredClasses,
                          newBlockedIntervals, completeBlocks,
                          lowerBound, upperBound)
          } orElse {
            // Case 2: use this term
            val (newLowerBound, newUpperBound) =
              if (selectedTerms.isEmpty)
                (lb, ub)
              else
                (lowerBound min lb, upperBound max ub)
            if (blockedIntervals.exists(p =>
                  newLowerBound <= p._1 && p._2 <= newUpperBound)) {
              // since the new interval includes some blocked interval, do not
              // choose this term
              None
            } else {
              var newSelectedTerms  = index :: selectedTerms
              var newCoveredClasses = coveredClasses + cl

              val (selTerms, otherTerms2) = otherTerms.partition {
                case ((cl, l, u), _) =>
                  (newLowerBound <= l && u <= newUpperBound) ||
                  newCoveredClasses(cl)
              }
              for (((cl2, _, _), index2) <- selTerms)
                if (!newCoveredClasses(cl2)) {
                  newCoveredClasses = newCoveredClasses + cl2
                  newSelectedTerms  = index2 :: newSelectedTerms
                }

              val newLowerBoundInc = newLowerBound + (newSelectedTerms.size - 1)
              if (newLowerBoundInc > newUpperBound) {
                // found a conflict
                Some(newSelectedTerms)
              } else {
                if (newLowerBoundInc == newUpperBound) {
                  // the range between lowerBound and upperBound is completely
                  // occupied
                  completeBlocks +=
                    ((newSelectedTerms.toSet, newLowerBound, newUpperBound))
                }

                findConflicts(otherTerms2, newSelectedTerms, newCoveredClasses,
                              blockedIntervals, completeBlocks,
                              newLowerBound, newUpperBound)
              }
            }
          }
        }
      }
    }

/*
  println(findConflicts(terms))
  println(findConflicts(terms2))
  println(findConflicts(terms3))
  println(findConflicts(terms4))
*/

/*
  type ClassTable = List[Seq[(Int, IdealInt, IdealInt)]]

  def findConflicts2(classes       : ClassTable,
                     chosenTerms   : List[Int],
                     blockedBounds : List[(IdealInt, IdealInt)],
                     lowerBound    : IdealInt,
                     upperBound    : IdealInt)
                                   : Option[List[Int]] =
    classes match {
      case List() =>
        None
      case terms :: otherClasses => {
        terms.find({ case (t, lb, ub) =>
                       lb >= lowerBound && ub <= upperBound }) match {

        }
      }
    }
*/
}

object AllDiffTheory {

  object Splitter extends Enumeration {
    val None, Disequations, ValueEnumerator = Value
  }

}

class AllDiffTheory(name     : String,
                    splitter : AllDiffTheory.Splitter.Value) extends Theory {
  import AllDiffTheory._

  /**
   * Theory function mapping an id and a term to the number of the class that
   * the term belongs to. By stating, e.g.,
   * <code>cl(0, s, 1) & cl(0, t, 2)</code>
   * it is implied that <code>s</code> and <code>t</code> have to be distinct.
   */
  val cl =
    MonoSortedIFunction(s"cl_$name", List(Sort.Integer, Sort.Integer), Sort.Integer,
                        true, false)

  val enumTheory =
    splitter match {
      case Splitter.ValueEnumerator =>
        Some(new IntValueEnumTheory(s"enum_$name"))
      case _ =>
        None
    }

  def distinct(ts : Seq[ITerm]) : IFormula = {
    import IExpression._
    val id = v(0)
    val shiftedTS = ts.map(shiftVars(_, 0, 1))
    val clFors =
      ex(and(for ((t, n) <- shiftedTS.zipWithIndex) yield cl(id, t) === n))
    val splitting =
      splitter match {
        case Splitter.None =>
          i(true)
        case Splitter.Disequations =>
          IExpression.distinct(ts)
        case Splitter.ValueEnumerator =>
          and(ts.map(enumTheory.get.enumIntValuesOf(_)))
      }
    clFors &&& splitting
  }

  val functions =
    List(cl)

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  val totalityAxioms =
    Conjunction.TRUE

  val functionalPredicates: Set[ap.parser.IExpression.Predicate] =
    predicates.toSet

  private val _cl = functionTranslation(cl)

  val functionPredicateMapping =
    functions zip (functions map functionTranslation)

  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  val plugin = Some(Propagator)

  object Propagator extends Plugin {
    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val clAtoms = goal.facts.predConj.positiveLitsWithPred(_cl)
      boundPropagation(goal, clAtoms)
    }
  }

  def boundPropagation(goal    : Goal,
                       clAtoms : IndexedSeq[Atom]) : Seq[Plugin.Action] =
    // TODO: make deterministic
    for ((id, atoms) <- clAtoms.groupBy(_(0)).toSeq;
         a <- boundPropagationPerId(goal, atoms))
    yield a

  def boundPropagationPerId(goal    : Goal,
                            clAtoms : IndexedSeq[Atom]) : Seq[Plugin.Action] = {
    println(clAtoms)
    Seq()
  }

  override val dependencies = enumTheory.toSeq

  override def isSoundForSat(
    theories : Seq[Theory],
    config : Theory.SatSoundnessConfig.Value) : Boolean = true

  override def toString = name

  TheoryRegistry register this

}

object TestAllDiff extends App {
  import ap.SimpleAPI
  import IExpression._

  val allDiff = new AllDiffTheory("allDiff", AllDiffTheory.Splitter.Disequations)

  SimpleAPI.withProver(enableAssert = false) { p =>
    import p._

    val N = 100
    val consts = createConstants("x", 0 until N, 0 until 1000)

    val startTime = System.currentTimeMillis

    val ad = allDiff.distinct(consts)
    println(ad)

    !! (ad)
    println(???)
    println(partialModel)

    val endTime = System.currentTimeMillis

    println(s"${endTime - startTime}ms")
  }

}

object Sudoku extends App {
  import ap.SimpleAPI

  SimpleAPI.withProver { p =>
    import p._
    import IExpression._

    println("Solving Sudoku ...")

    val allDiff = new AllDiffTheory("allDiff", AllDiffTheory.Splitter.None)
    val enumTheory = new IntValueEnumTheory("enum")
    import allDiff.distinct

//    setConstructProofs(true)

    val startTime = System.currentTimeMillis

    // declare 9x9 variables, each ranging from 1 to 9
    val rows = for (row <- 0 until 9) yield createConstants(9, 1 to 9)

//    for (row <- rows; c <- row)
//      !! (enumTheory.enumIntValuesOf(c))

    !! (and(rows map distinct))
    !! (and(for (col <- 0 until 9)
            yield distinct(for (row <- 0 until 9) yield rows(row)(col))))

    !! (and(for (rblock <- 0 until 3; cblock <- 0 until 3)
            yield distinct(for (row <- 0 until 3; col <- 0 until 3)
                            yield rows(rblock*3 + row)(cblock*3 + col))))

    !! (rows(0)(0) === 7)
    !! (rows(0)(2) === 4)
    !! (rows(1)(0) === 9)
    !! (rows(1)(1) === 1)

    !! (rows(1)(5) === 7)

    !! (rows(1)(6) === 6)
    !! (rows(1)(7) === 8)
    !! (rows(0)(8) === 5)

    !! (rows(3)(1) === 3)
    !! (rows(5)(1) === 4)

    !! (rows(3)(4) === 2)
    !! (rows(4)(3) === 3)
    !! (rows(5)(4) === 8)

    !! (rows(3)(7) === 5)
    !! (rows(5)(6) === 3)

    !! (rows(6)(2) === 2)
    !! (rows(8)(2) === 9)

    println(???)

    ??? match {
      case SimpleAPI.ProverStatus.Sat =>
        for (row <- rows)
          println((row map eval) mkString " ")
      case SimpleAPI.ProverStatus.Unsat =>
        println("Unsat")
    }

    val endTime = System.currentTimeMillis

    println(s"${endTime - startTime}ms")
  }
}