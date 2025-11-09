/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer <ph_r@gmx.net>
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

// Unit tests for bit-wise bit-vectors operations

package ap.theories.bitvectors

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._
import ap.util.ExtraAssertions

class TestBitwise extends Properties("TestBitwise") {
  import IExpression._
  import ModuloArithmetic._

  property("bvand") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))
      val b2 = createConstant("b2", UnsignedBVSort(32))
      val b3 = createConstant("b3", UnsignedBVSort(32))
      
      !! (b3 === bvand(b1, b2))
      ??? == ProverStatus.Sat
    }
  }

  property("extract1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))

      !! (bvuge(b1, bv(32, 0x00FF0000)))
      !! (bvule(b1, bv(32, 0x00FFFFFF)))

      scope {
        !! (extract(19, 12, b1) === bv(8, 0xFF))
        assert(??? == ProverStatus.Sat)
      }

      scope {
        ?? (bvugt(extract(16, 15, b1), bv(2, 0)))
        assert(??? == ProverStatus.Valid)
      }

      true
    }
  }

  property("extract2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x = createConstant("x")

      scope {
        !! (bvugt(extract(2, 1, 32*x + 3), bv(2, 0)))
        assert(??? == ProverStatus.Sat)
      }

      scope {
        !! (bvugt(extract(5, 3, 8*x + 3), bv(3, 0)))
        assert(??? == ProverStatus.Sat)
      }

      true
    }
  }

}
