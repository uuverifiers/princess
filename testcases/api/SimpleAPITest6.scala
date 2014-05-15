/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.proof.goal.Goal
import ap.terfor.{TerForConvenience, Formula}
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.conjunctions.Conjunction
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}

import scala.collection.mutable.ArrayBuffer

object SimpleAPITest6 extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus
  import p._

  val square = createFunction("square", 1)
  val squarePred = asConjunction(square(0) === 0).predicates.iterator.next

  //////////////////////////////////////////////////////////////////////////////

  /**
   * A procedure systematically splitting over the input domain
   * of the square function
   */
  object Splitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      val squareLits = goal.facts.predConj.positiveLitsWithPred(squarePred)
      val aConj = conj(goal.facts.arithConj)

      val splits = new ArrayBuffer[(Conjunction, Conjunction, IdealInt)]

      for (a <- squareLits) {
        (PresburgerTools.lowerBound(a(0), aConj),
         PresburgerTools.lowerBound(-a(0), aConj)) match {
          case (Some(lb), Some(ubM)) if (lb == -ubM) =>
            // nothing
          case (Some(lb), Some(ubM)) => {
            val sum = lb - ubM
            val thres = sum.signum match {
              case -1 => -((-sum + 1) / 2)
              case _ => sum / 2
            }
            splits += ((a(0) <= thres, a(0) > thres, thres))
          }
          case (Some(lb), None) if (lb.signum >= 0) => {
            val thres = (lb + 1) * 2
            splits += ((a(0) <= thres, a(0) > thres, thres))
          }
          case (None, Some(ubM)) if (ubM.signum >= 0) => {
            val thres = (-ubM - 1) * 2
            splits += ((a(0) > thres, a(0) <= thres, thres))
          }
          case _ => {
            splits += ((a(0) <= 0, a(0) > 0, 0))
          }
        }
      }

      if (splits.isEmpty) {
        List()
      } else {
        val (left, right, _) = splits.toList minBy (_._3.abs)
        List(Plugin.SplitGoal(List(List(Plugin.AddFormula(!left)),
                                   List(Plugin.AddFormula(!right)))))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * (Forward) interval propagation for the square function
   */
  object Propagator extends Plugin {
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None
    
    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      val squareLits = goal.facts.predConj.positiveLitsWithPred(squarePred)
      val aConj = conj(goal.facts.arithConj)

      val newBounds = new ArrayBuffer[Formula]
      for (a <- squareLits) {
        newBounds += (a(1) >= 0)

        (PresburgerTools.lowerBound(a(0), aConj),
         PresburgerTools.lowerBound(-a(0), aConj)) match {
          case (Some(lb), Some(ubM)) if (lb.signum >= 0) => {
            newBounds += (a(1) >= (lb * lb))
            newBounds += (a(1) <= (ubM * ubM))
          }
          case (Some(lb), Some(ubM)) if (ubM.signum >= 0) => {
            newBounds += (a(1) <= (lb * lb))
            newBounds += (a(1) >= (ubM * ubM))
          }
          case (Some(lb), Some(ubM)) => {
            val bMax = lb max ubM.abs
            newBounds += (a(1) <= (bMax * bMax))
          }
          case (Some(lb), None) if (lb.signum >= 0) => {
            newBounds += (a(1) >= (lb * lb))
          }
          case (None, Some(ubM)) if (ubM.signum >= 0) => {
            newBounds += (a(1) >= (ubM * ubM))
          }
          case _ => {
            // nothing
          }
        }

        // similarly, backward propagation could be implemented ...
      }

      val newFor = goal reduceWithFacts conj(newBounds)

      if (newFor.isTrue) {
        if (squareLits forall { a => a(0).isConstant })
          List()
        else
          // schedule splitting as a delayed task
          List(Plugin.ScheduleTask(Splitter, 0))
      } else {
        List(Plugin.AddFormula(!newFor))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  setupTheoryPlugin(Propagator)

  val x = createConstant("x")
  val k = createConstant("k")

  scope {
    !! (square(x) >= 100)
    !! (x >= 3)

    println(???)  // Sat

    !! (x <= 5)
    println(???)  // Unsat
  }

  scope {
    !! (k >= 0)
    !! (square(x) === 100 + k * 5)
    !! (x >= 3)

    println(???)                                    // Sat
    println("x = " + eval(x) + ", k = " + eval(k))  // x = 10, k = 0

    !! (x =/= eval(x))
    println(???)                                    // Sat
    println("x = " + eval(x) + ", k = " + eval(k))  // x = 15, k = 25
  }

  p.shutDown
}
