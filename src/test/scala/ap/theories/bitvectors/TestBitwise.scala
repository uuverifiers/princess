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
      val y = createConstant("y", Sort.Nat)

      scope {
        !! (bvugt(extract(2, 1, 32*x + 3), bv(2, 0)))
        assert(??? == ProverStatus.Sat)
      }

      scope {
        !! (bvugt(extract(5, 3, 8*y + 3), bv(3, 0)))
        assert(??? == ProverStatus.Sat)
      }

      true
    }
  }

  property("extract3") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val q = createRelation("q", List(UnsignedBVSort(32)))
      val y = createConstant("y", UnsignedBVSort(32))

      scope {
        !! (q(y))
        !! (bvuge(extract(5, 3, y), bv(3, 5)))
        !! (bvuge(extract(12, 11, y), bv(2, 2)))
        !! (bvule(extract(23, 20, y), bv(4, 10)))
        !! (bvuge(y, bv(32, 1000)))
        !! (bvule(y, bv(32, 100000000)))
        assert(??? == ProverStatus.Sat)
      }

      true
    }
  }

  property("extract4") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val q = createRelation("q", List(UnsignedBVSort(8)))
      val y = createConstant("y", UnsignedBVSort(8))

      scope {
        !! (!q(167))
        !! (q(y))
        !! (extract(7, 4, y) === bv(4, 10))
        !! (extract(3, 0, y) === bv(4, 7))
        assert(??? == ProverStatus.Unsat)
      }

      true
    }
  }

  property("extract5") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val q = createRelation("q", List(UnsignedBVSort(8)))
      val y = createConstant("y", Sort.Interval(Some(-8), Some(-1)))

      scope {
        !! (!q(-3))
        !! (!q(-4))
        !! (q(y))
        !! (extract(1, 1, y) === bv(1, 0))
        !! (extract(2, 2, y) === bv(1, 1))
        assert(??? == ProverStatus.Unsat)
      }

      true
    }
  }

  property("extract6") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val y = createConstant("y", UnsignedBVSort(8))
      val z = createConstant("z", UnsignedBVSort(4))

      scope {
        !! (y >= 25)
        !! (y <= 230)
        !! (extract(7, 4, y) === z)
        assert(??? == ProverStatus.Sat)
      }

      true
    }
  }

}
