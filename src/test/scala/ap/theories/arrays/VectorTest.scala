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
import ap.theories.GroebnerMultiplication
import ap.theories.arrays._

import org.scalacheck.Properties
import ap.util.ExtraAssertions

class VectorTest extends Properties("VectorTest") with ExtraAssertions {

  val expectedOutput = """Sat
Sat
v = store(const(12), 2, 1)
w = store(const(22), 2, 11)
Unsat
Valid
Valid
Sat
Unsat
Unsat
Sat
v = const(0)
w = const(1)
Unsat
Unsat
"""

  import IExpression._

  property("vectortest") = checkOutput(expectedOutput) {

  ap.util.Debug.enableAllAssertions(true)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(0) + v(1) === v(2)),
    CombArray.CombinatorSpec("vec_times", List(0, 0), 0,
                             GroebnerMultiplication.mul(v(0), v(1)) === v(2)),
    CombArray.CombinatorSpec("vec_plus1", List(0), 0,
                             v(0) + 1 === v(1))
  )

  val VectorTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Sort.Integer)),
                  vectorOps, List(GroebnerMultiplication))

  val Seq(intVector)                      = VectorTheory.arraySorts
  val Seq(vec_plus, vec_times, vec_plus1) = VectorTheory.combinators
  val vec_select                          = VectorTheory.subTheories(0).select
  val vec_store                           = VectorTheory.subTheories(0).store
  val vec_const                           = VectorTheory.subTheories(0).const

  def vec(ts : ITerm*) : ITerm = {
    var res : ITerm = vec_const(0)
    for ((t, n) <- ts.zipWithIndex)
      res = vec_store(res, n, t)
    res
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(VectorTheory)

    val x = createConstant("x")
    val y = createConstant("y")
    val z = createConstant("z")
    val v = createConstant("v", intVector)
    val w = createConstant("w", intVector)

    scope {
      !! (vec_select(v, 2) > 0)
      println(???) // sat

      !! (w === vec_plus(v, vec_const(10)))
      println(???) // sat

      withCompleteModel { eval =>
        for (x <- List(v, w))
          println("" + x + " = " + eval(x))
      }

      !! (vec_select(w, 2) < 2)
      println(???) // unsat
    }

    scope {
      !! (v === vec_const(1))
      !! (w === vec_plus(v, v))
      ?? (vec_select(w, x) === 2)
      println(???) // valid
    }

    scope {
      ?? (vec_plus(vec_const(2), vec_const(2)) ===
            vec_times(vec_const(2), vec_const(2)))
      println(???) // valid
    }

    scope {
      val a = vec(x, y, z)
      val b = vec(3, 2, 1)
      !! (vec_times(a, vec_const(-1)) === b)
      println(???) // sat
    }

    scope {
      !! (v === vec_const(1))
      !! (w === vec_const(3))
      !! (w === vec_plus(v, v))
      println(???) // unsat
    }

    scope {
      val u = createConstant("u", intVector)
      !! (v === vec_const(1))
      !! (w === vec_const(3))
      !! (u === vec_store(w, 0, 3))
      !! (u === vec_plus(v, v))
      println(???) // unsat
    }

    scope {
      !! (w === vec_plus(v, w))
      println(???) // sat
      withCompleteModel { eval =>
        for (x <- List(v, w))
          println("" + x + " = " + eval(x))
      }
      !! (vec_select(v, 10) > 10)
      println(???) // unsat
    }

    scope {
      !! (w === vec_plus1(v))
      !! (v === vec_plus1(w))
      println(???) // unsat
    }
  }
  }
}
