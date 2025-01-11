/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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
import SimpleAPI.ProverStatus
import ap.parser._

import org.scalacheck.Properties

class MinMaxTest extends Properties("MinMaxTest") {

  import IExpression._

  val ArTheory = new MinMaxArray(List(Sort.Integer))

  property("simple") = {
    ap.util.Debug.enableAllAssertions(true)

    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      
      val a = createConstant("a", ArTheory.sort)
      val b = createConstant("b", ArTheory.sort)

      scope {
        !! (ArTheory.max(a) === 10)
        !! (ArTheory.min(a) === -10)
        assert(??? == ProverStatus.Sat)

        !! (b === ArTheory.store(a, 0, 42))
        assert(??? == ProverStatus.Sat)

        ?? (ArTheory.max(b) === 42)
        assert(??? == ProverStatus.Valid)
      }

      scope {
        ?? (ArTheory.min(a) <= ArTheory.max(a))
        assert(??? == ProverStatus.Valid)
      }

      true
    }
  }

  property("interpolation") = {
    ap.util.Debug.enableAllAssertions(true)

    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      
      val a = createConstant("a", ArTheory.sort)
      val b = createConstant("b", ArTheory.sort)

      setConstructProofs(true)

      scope {
        setPartitionNumber(1)
        !! (ArTheory.max(a) === 10)
        setPartitionNumber(2)
        !! (ArTheory.select(a, 42) === 11)
        assert(??? == ProverStatus.Unsat)
        assert(getInterpolants(List(Set(1), Set(2)))(0).toString ==
                 "!(select(a, 42) = 11)")
      }

      scope {
        setPartitionNumber(1)
        !! (ArTheory.max(a) === 10)
        setPartitionNumber(2)
        !! (ArTheory.min(a) === 11)
        assert(??? == ProverStatus.Unsat)
        assert(getInterpolants(List(Set(1), Set(2)))(0).toString ==
                 "EX (select(a, _0) = 10)")
      }

      scope {
        setPartitionNumber(1)
        !! (ArTheory.max(a) === 10)
        setPartitionNumber(2)
        !! (b === ArTheory.store(a, 100, 101))
        setPartitionNumber(3)
        !! (ArTheory.select(b, 0) === 102)
        assert(??? == ProverStatus.Unsat)
        assert(getInterpolants(List(Set(1), Set(2), Set(3))).map(_.toString) ==
                 Seq("!(select(a, 0) = 102)", "!(select(b, 0) = 102)"))
      }

      true
    }
  }
}