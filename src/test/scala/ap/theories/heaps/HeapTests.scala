/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer, Zafer Esen
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

package ap.theories.heaps

import ap.theories.ADT
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parameters.Param.InputFormat
import ap.types._
import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._

object HeapTests {
class PrincessTester (p : SimpleAPI) {
  import p._

  var testCaseCounter = 1;

  private def expect[A](x : A, expected : A) : (A, Boolean) = {
    println(x)
    assert(x == expected)
    (x, x == expected)
  }

  abstract sealed class TestStep (val fs : IFormula*)
  case class SatStep(override val fs : IFormula*) extends TestStep
  case class UnsatStep(override val fs : IFormula*) extends TestStep
  case class CommonAssert (override val fs : IFormula*) extends TestStep

  private def printModel {
    val newLine = "\n" + " "*2
    println {"Model:" + newLine +
             (for ((l, v) <- partialModel.interpretation.iterator)
               yield {
                 l + " -> " + v
               }).mkString(newLine)
    }
  }

  private def justAssert(s : TestStep) = {
    for (f <- s.fs) {
      addAssertion(f)
      print("  ")
      PrincessLineariser printExpression f
      println
    }
  }

  private def executeStep(ps : ProverStatus.Value, s : TestStep) : Boolean = {
    var res = false
    scope {
      for (f <- s.fs) {
        addAssertion(f)
        print("  ")
        PrincessLineariser printExpression f
        if (s.fs.last != f) println(" &")
      }
      print(" --> ")
      val (proverResult, passed) = expect(???, ps)
      res = passed
      //if (passed && proverResult == ProverStatus.Sat) printModel
      //else if (passed && proverResult == ProverStatus.Unsat)
      //  println(certificateAsString(Map.empty,
      //    InputFormat.Princess))
    }
    res
  }

  def TestCase(name : String, steps : TestStep*) {
    println("=" * 80)
    println(
      "Test " + testCaseCounter + ": " + name)
    println("-" * 80)
    var stepNo = 1;
    scope {
      for (s <- steps) {
        if (s.isInstanceOf[CommonAssert]) {
          println("-" * 80)
          println("Common assertion: ")
          justAssert(s)
          println("-" * 80)
        } else {
          print("Step " + testCaseCounter + "." + stepNo + " (expected: ")
          stepNo = stepNo + 1
          s match {
            case _ : SatStep => println("Sat)")
              executeStep(ProverStatus.Sat, s)
            case _ : UnsatStep => println("Unsat)")
              executeStep(ProverStatus.Unsat, s)
            case _ => // do nothing as CommonAssert step is already handled
          }
          if (steps.last != s) println("-" * 80)
        }
      }
      println("=" * 80)
      testCaseCounter = testCaseCounter + 1
    }
  }
}

  def measureTime[A](msg: String)(comp : => A) : A = {
    print(f"$msg: ")
    val start = System.currentTimeMillis
    val res : A = comp
    val stop = System.currentTimeMillis
    println(f"${stop - start}ms")
    res
  }

}
