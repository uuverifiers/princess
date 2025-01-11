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
import ap.theories.rationals.Rationals
import ap.theories.arrays._

import org.scalacheck.Properties
import ap.util.ExtraAssertions

class RatTest extends Properties("RatTest") with ExtraAssertions {

  val expectedOutput = """Sat
x = 0
v = store(const(Rat_fromRing(3)), 2, Rat_fromRing(1))
w = store(const(Rat_fromRing(3)), 2, Rat_fromRing(1))
Sat
x = 0
v = store(const(Rat_fromRing(3)), 2, Rat_fromRing(1))
w = store(const(Rat_fromRing(4)), 2, Rat_fromRing(2))
Unsat
Valid
Valid
"""

  import IExpression._

  property("rattest") = checkOutput(expectedOutput) {
  ap.util.Debug.enableAllAssertions(true)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             Rationals.plus(v(0, Rationals.dom),
                                            v(1, Rationals.dom)) ===
                               v(2, Rationals.dom)),
    CombArray.CombinatorSpec("vec_times", List(0, 0), 0,
                             Rationals.mul(v(0, Rationals.dom),
                                           v(1, Rationals.dom)) ===
                               v(2, Rationals.dom))
  )

  val VectorTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Rationals.dom)),
                  vectorOps)

  val Seq(ratVector)           = VectorTheory.arraySorts
  val Seq(vec_plus, vec_times) = VectorTheory.combinators
  val vec_select               = VectorTheory.subTheories(0).select
  val vec_const                = VectorTheory.subTheories(0).const

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    // currently leading to an exception
    addTheory(VectorTheory)

    val x = createConstant("x")
    val v = createConstant("v", ratVector)
    val w = createConstant("w", ratVector)

    scope {
      !! (Rationals.gt(vec_select(v, 2), Rationals.zero))
      println(???) // sat
      withCompleteModel { eval =>
        for (x <- List(x, v, w))
          println("" + x + " = " + eval(x))
      }

      !! (w === vec_plus(v, vec_const(Rationals.one)))
      println(???) // sat
      withCompleteModel { eval =>
        for (x <- List(x, v, w))
          println("" + x + " = " + eval(x))
      }

      !! (Rationals.lt(vec_select(w, 2), Rationals.one))
      println(???) // unsat
    }

    scope {
      !! (v === vec_const(Rationals.one))
      !! (w === vec_plus(v, v))
      ?? (vec_select(w, x) === Rationals.int2ring(2))
      println(???) // valid
    }

    scope {
      ?? (vec_plus(vec_const(Rationals.int2ring(2)),
                   vec_const(Rationals.int2ring(2))) ===
            vec_times(vec_const(Rationals.int2ring(2)),
                      vec_const(Rationals.int2ring(2))))
      println(???) // valid
    }
  }
  }
}
