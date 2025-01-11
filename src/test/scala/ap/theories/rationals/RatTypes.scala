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

import org.scalacheck.Properties
import ap.util.Prop._

class RatTypes extends Properties("RatTypes") {

  property("types") =
    SimpleAPI.withProver(enableAssert = true) { p =>
      ap.util.Debug.enableAllAssertions(true)
      import p._
      import Rationals.{dom => Rat}
      import IExpression._

      scope {
        val a = createConstant("a", Rat)
        val b = createConstant("b", Rat)
        val f1 = Rationals.plus(a, b)
        assertEquals(Sort.sortOf(f1), Rat)
      }

      scope {
        val a = createConstant("a", Rat)
        val b = Rationals.Fraction(2, 1)
        val f1 = Rationals.mul(a, b)
        assertEquals(Sort.sortOf(f1), Rat)
      }

      scope {
        val a = createConstant("a", Rat)
        val b = Rationals.int2ring(2)
        val f1 = Rationals.mul(a, b)
        assertEquals(Sort.sortOf(f1), Rat)
      }

      scope {
        val a = createConstant("a", Rat)
        val b = createConstant("b", Rat)
        val f1 = Rationals.div(a, b)
        assertEquals(Sort.sortOf(f1), Rat)
      }

      scope {
        val a = createConstant("a", Rat)
        val b = createConstant("b", Rat)
        val f1 = Rationals.plus(a, b)
        val c = createBooleanVariable("c")
        val d = Rationals.Fraction(2, 1)
        val f2 = ite(c, f1, d)
        assertEquals(Sort.sortOf(f1), Rat)
        assertEquals(Sort.sortOf(f2), Rat)
      }

      scope {
        val a = createConstant("a", Rat)
        val b = Rationals.int2ring(0)
        val f1 = Rationals.mul(a, b)
        assertEquals(Sort.sortOf(f1), Rat)
      }

      true
    }

}
