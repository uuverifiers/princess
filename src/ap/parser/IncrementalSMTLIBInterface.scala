/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.Prover
import ap.parameters.{GlobalSettings, Param}

import scala.collection.mutable.Stack

object IncrementalSMTLIBInterface {

  class InterfaceException(msg : String) extends Exception(msg)

  private val Push      = """ *\( *push +([0-9]+) *\) *""".r
  private val Pop       = """ *\( *pop +([0-9]+) *\) *""".r
  private val CheckSat  = """ *\( *check-sat *\) *""".r
  private val Exit      = """ *\( *exit *\) *""".r
  private val Reset     = """ *\( *reset *\) *""".r
  private val GetValue  = """ *\( *get-value (.*)\) *""".r
  private val GetInts   = """ *\( *get-interpolants *\) *""".r

}

abstract class IncrementalSMTLIBInterface {

  import IncrementalSMTLIBInterface._

  protected def solve(input : String) : Option[Prover.Result]

  private val runningInput = new StringBuffer
  private val backtrackingStack = new Stack[Int]

  private var lastResult : Option[Prover.Result] = None
  
  def readInputs(inputs : java.io.BufferedReader,
                 settings : GlobalSettings) : Unit = {
    var line = inputs.readLine
    while (line != null) {
      line match {
        case Push(numStr) =>
          for (_ <- 0 until numStr.toInt)
            backtrackingStack push runningInput.length
        case Pop(numStr) =>
          for (_ <- 0 until numStr.toInt)
            runningInput setLength backtrackingStack.pop
        case CheckSat() =>
          lastResult = solve(runningInput.toString)
        case Exit() =>
          return
        case Reset() => {
          runningInput setLength 0
          backtrackingStack.clear
        }

        case GetValue(termsStr) => lastResult match {
          case Some(Prover.CounterModel(model)) =>
            for (t <- termsStr split ' ') if (!t.isEmpty) {
              print("(" + t + " ")

              // search the model for the value of this symbol
              val remModel = new Stack[IFormula]
              remModel push model
              var found = false
              while (!remModel.isEmpty && !found) remModel.pop match {
                case IBinFormula(IBinJunctor.And, left, right) => {
                  remModel push left
                  remModel push right
                }
                case IAtom(p, Seq()) if (p.name == t) => {
                  print("true")
                  found = true
                }
                case INot(IAtom(p, Seq())) if (p.name == t) => {
                  print("false")
                  found = true
                }
                case _ => // nothing
              }
              if (!found) {
                print("false")
                Console.err.println("value of " + t + " is unknown, assigning to false")
              }
              println(")")
            }
          case _ => {
            println("error")
            Console.err.println("no model available")
          }
        }

        case GetInts() => lastResult match {
          case Some(Prover.NoCounterModelCertInter(_, interpolants)) => {
            val timeBefore = System.currentTimeMillis
            Console.withOut(Console.err) {
              if (Param.LOGO(settings))
                println
              println("Interpolating ...")
            }
 
            for (i <- interpolants) {
              SMTLineariser(i)
              println
            }

            Console.withOut(Console.err) {
              println
              if (Param.LOGO(settings))
                println("" + (System.currentTimeMillis - timeBefore) + "ms")
            }
          }
          case _ => {
            println("error")
            Console.err.println("no interpolants available")
          }
        }

        case _ => {
          runningInput append line
          runningInput append '\n'
        }
      }
      line = inputs.readLine
    }
  }

}