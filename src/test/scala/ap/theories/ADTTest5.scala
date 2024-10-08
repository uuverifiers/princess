/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2021-2024 Philipp Ruemmer <ph_r@gmx.net>
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

//object ADTTest5 extends App {
  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ADT._
  import ap.types.Sort
  import ap.util.Debug

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class ADTTest5 extends Properties("ADTTest5") with ExtraAssertions {

  val expectedOutput = """Test 1
Sat
tuple(const(0))
Sat
tuple(const(0))
tuple(const(0))
Test 2
Sat
tuple(store(const(0), 0, 1))
tuple(const(0))
Test 3
Sat
tuple(store(const(13), 1, 11))
tuple(const(0))
"""

  property("ADTTest5") = checkOutput(expectedOutput) {

  Debug enableAllAssertions true

  val ar = ExtArray(List(Sort.Integer), Sort.Integer)

  val adt =
    new ADT (List("tuple"),
             List(("tuple",
                   CtorSignature(List(("t1", OtherSort(ar.sort))),
                                 ADTSort(0)))))

  val Seq(tupleSort) = adt.sorts
  val Seq(tuple)     = adt.constructors
  val Seq(Seq(t1))   = adt.selectors

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val c = createConstant("c", tupleSort)
    val d = createConstant("d", tupleSort)

    import IExpression._

    println("Test 1")
    scope {
      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(c))

      !! (c === d)
      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(c))
      println(evalToTerm(d))
    }

    println("Test 2")
    scope {
      !! (c =/= d)
      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(c))
      println(evalToTerm(d))
    }

    println("Test 3")
    scope {
      !! (ar.select(t1(d), 1) > 10)
      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(d))
      println(evalToTerm(c))
    }

  }
}
}