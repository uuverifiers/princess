/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.theories.arrays._

import org.scalacheck.Properties
import ap.util.ExtraAssertions

class PairTest extends Properties("PairTest") with ExtraAssertions {

  val expectedOutput = """Valid
Invalid
a = store(const(43), 42, 1)
b = const(false)
c = const(0)
Sat
a = store(store(const(43), 41, 44), 42, 1)
b = store(const(true), 42, false)
c = store(store(const(43), 41, 44), 42, 0)
Valid
Sat
"""

  property("pairtest") = checkOutput(expectedOutput) {
  ap.util.Debug.enableAllAssertions(true)

  import IExpression._

  val (pairSort, pair, Seq(f1, f2)) =
    ADT.createRecordType("pair", List(("f1", Sort.Integer),
                                      ("f2", Sort.Integer)))

  val vectorOps = Vector(
    CombArray.CombinatorSpec("mask", List(0, 1), 0,
                             (eqZero(v(1)) & (v(2) === v(0))) |
                             (!eqZero(v(1)) & (v(2) === 0))),
    CombArray.CombinatorSpec("zip", List(0, 0), 2,
                             v(2) === pair(v(0), v(1)))
  )

  val VTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Sort.Integer),
                         new ExtArray(List(Sort.Integer), Sort.Bool),
                         new ExtArray(List(Sort.Integer), pairSort)),
                  vectorOps)

  val Seq(intArray, boolArray, pairArray) = VTheory.arraySorts
  val Seq(mask, zip)                      = VTheory.combinators
  val int_select                          = VTheory.subTheories(0).select
  val bool_select                         = VTheory.subTheories(1).select
  val pair_select                         = VTheory.subTheories(2).select

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(VTheory)

    val a = createConstant("a", intArray)
    val b = createConstant("b", boolArray)
    val c = createConstant("c", intArray)
    val d = createConstant("d", pairArray)

    val q = createConstant("q", pairSort)

    scope {
      !! (c === mask(a, b))
      !! (int_select(a, 42) > 0)

      scope {
        !! (bool_select(b, 42) === 0)
        ?? (int_select(c, 42) > 0)
        println(???) // valid
      }

      !! (bool_select(b, 42) === 1)

      scope {
        ?? (int_select(c, 42) > 0)
        println(???) // invalid
        withCompleteModel { eval =>
          for (x <- List(a, b, c))
            println("" + x + " = " + eval(x))
        }
      }

      scope {
        !! (bool_select(b, 41) === 0)
        println(???)
        withCompleteModel { eval =>
          for (x <- List(a, b, c))
            println("" + x + " = " + eval(x))
        }
      }

      scope {
        !! (d === zip(a, c))
        !! (q === pair_select(d, 42))
        ?? (f1(q) > 0 & f2(q) === 0)
        println(???) // valid
      }
//    println(evalToTerm(q))
    }

    scope {
      !! (q === pair(1, 2))
      println(???) // Sat
//      println(partialModel)
    }

  }
}

}
