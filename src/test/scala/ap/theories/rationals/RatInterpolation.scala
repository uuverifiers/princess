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

package ap.theories.rationals

import ap.parser._
import ap.SimpleAPI
import SimpleAPI.ProverStatus

import org.scalacheck.Properties

class RatInterpolation extends Properties("RatInterpolation") {

  property("simple1") =
  SimpleAPI.withProver(enableAssert = true) { p =>
    ap.util.Debug.enableAllAssertions(true)
    import p._
    import IExpression._
    import Rationals.{Fraction, int2ring => int2rat}

    setConstructProofs(true)

    val x = createConstant("x", Rationals.dom)
    val y = createConstant("y", Rationals.dom)
    val z = createConstant("z", Rationals.dom)

    scope {
      setPartitionNumber(1)
      !! (Rationals.lt(x, y) & Rationals.lt(y, z))
      setPartitionNumber(2)
      !! (x === Rationals.plus(z, int2rat(5)))

      assert(??? == ProverStatus.Unsat)
      assert(getInterpolants(List(Set(1), Set(2)))(0).toString ==
               "((-2 + (z + -1 * x)) >= 0)")
    }

    scope {
      setPartitionNumber(1)
      !! (y === Rationals.plus(x, int2rat(1)))
      !! (z === Rationals.plus(y, Fraction(1, 2)))
      setPartitionNumber(2)
      !! (z =/= Rationals.plus(x, Fraction(3, 2)))

      assert(??? == ProverStatus.Unsat)
      assert(getInterpolants(List(Set(1), Set(2)))(0).toString ==
               "((3 * Rat_denom + (-2 * z + 2 * x)) = 0)")
    }

    scope {
      setPartitionNumber(1)
//      !! (y === Rationals.plus(Rationals.mul(Fraction(1, 2), x), int2rat(1)))
      !! (Rationals.times(2, y) === Rationals.plus(x, int2rat(2)))
//      !! (z === Rationals.plus(y, Fraction(1, 2)))
      !! (Rationals.times(2, z) === Rationals.plus(Rationals.times(2, y), int2rat(1)))
      setPartitionNumber(2)
//      !! (z =/= Rationals.plus(Rationals.mul(Fraction(1, 2), x), Fraction(3, 2)))
      !! (Rationals.times(2, z) =/= Rationals.plus(x, int2rat(3)))

      assert(??? == ProverStatus.Unsat)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    true
  }

}
