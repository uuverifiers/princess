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
import ap.parameters.{Param, GlobalSettings}

import org.scalacheck.Properties
import ap.util.Prop._
import ap.util.ExtraAssertions

object TestBitwise {
  val loggingSettings =
    Param.LOG_LEVEL.set(GlobalSettings.DEFAULT, Set(Param.LOG_TASKS))
}

class TestBitwise extends Properties("TestBitwise") {
  import IExpression._
  import ModuloArithmetic._

  property("bvand1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(8))
      val b2 = createConstant("b2", UnsignedBVSort(8))
      val b3 = createConstant("b3", UnsignedBVSort(8))
      
      !! (b3 === bvand(b1, b2))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))
      val b3 = createConstant("b3", UnsignedBVSort(32))
      
      !! (b3 === bvand(b1, bv(32, 0xF0F0)))
      assert(??? == ProverStatus.Sat)

      !! (b3 === bvand(bv(32, 0x0F0F), b1))
      assert(??? == ProverStatus.Sat)

      ?? (extract(15, 0, b1) === 0)
      assert(??? == ProverStatus.Valid)

      true
    }
  }

  property("bvand3") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))
      val b2 = createConstant("b2", UnsignedBVSort(32))
      val b3 = createConstant("b3", UnsignedBVSort(32))
      
      !! (b1 === bv(32, 0xF0F0F0F0))
      !! (b2 === bv(32, 0x0000FFFF))
      !! (b3 === bvand(b1, b2))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand4") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))
      val b2 = createConstant("b2", UnsignedBVSort(32))
      val b3 = createConstant("b3", UnsignedBVSort(32))
      
      !! ((b1 === bv(32, 0x0000FFFF)) | (b2 === bv(32, 0x0000000F)))
      !! (b3 === bvand(b1, b2))
      assert(??? == ProverStatus.Sat)

      ?? (b3 <= 0xFFFF)
      ??? == ProverStatus.Valid
    }
   }

  property("bvand5") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(1))
      val b2 = createConstant("b2", UnsignedBVSort(1))
      val b3 = createConstant("b3", UnsignedBVSort(1))
      
      !! (b1 === bvand(b2, bvnot(b3)))
      ??? == ProverStatus.Sat
    }
   }

  property("bvand_add") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(2))
      val b2 = createConstant("b2", UnsignedBVSort(2))
      val b3 = createConstant("b3", UnsignedBVSort(2))
      val b4 = createConstant("b4", UnsignedBVSort(2))
      
      !! (b4 === bvand(b3, bvadd(b1, bv(2, 1))))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand_nested") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(4))
      val b2 = createConstant("b2", UnsignedBVSort(4))
      val b3 = createConstant("b3", UnsignedBVSort(4))
      val b4 = createConstant("b4", UnsignedBVSort(4))
      
      !! (b4 === bvand(b1, b2))
      !! (bvadd(b4, bv(4, 1)) === bvand(b1, b3))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand_not") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(4))
      val b2 = createConstant("b2", UnsignedBVSort(4))
      val b3 = createConstant("b3", UnsignedBVSort(2))
      val b4 = createConstant("b4", UnsignedBVSort(2))
      
      !! (b2 === 15 - b1)
      !! (b3 === extract(2, 1, b1))
      !! (b4 === extract(2, 1, b2))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand_not2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(4))
      val b3 = createConstant("b3", UnsignedBVSort(2))
      val b4 = createConstant("b4", UnsignedBVSort(2))
      
      !! (b3 === extract(2, 1, b1))
      !! (b4 === extract(2, 1, bvnot(b1)))
      assert(??? == ProverStatus.Sat)

      !! (b3 === b4)
      assert(??? == ProverStatus.Unsat)

      true
    }
  }

  property("bvand_rewrites") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(64))
      val b2 = createConstant("b2", UnsignedBVSort(64))
      val b3 = createConstant("b3", UnsignedBVSort(64))
      
      scope {
        // idempotence
        !! (b2 === bvand(b1, b1))
        !! (b2 =/= b1)
        assert(??? == ProverStatus.Unsat)
      }
      scope {
        // bvand with complementary arguments
        !! (b3 === pow2MinusOne(64) - b1)
        !! (b2 === bvand(b1, b3))
        !! (b2 > 0)
        assert(??? == ProverStatus.Unsat)
      }
      true
    }
  }

  property("bvand_unary") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(1))
      val b2 = createConstant("b2", UnsignedBVSort(1))
      val b3 = createConstant("b3", UnsignedBVSort(2))
      val b4 = createConstant("b4", UnsignedBVSort(2))
      val q = createRelation("q", 1)

      !! (b2 === bvand(b1, b1))
      !! (3 === bvand(b3, b4))
      !! (q(b1))
      !! (q(b2))
      ??? == ProverStatus.Sat
    }
  }

  property("bvand_bounds") = {
    try {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(32))
      val b2 = createConstant("b2", UnsignedBVSort(32))
      val b3 = createConstant("b3", UnsignedBVSort(32))

      !! (b3 === bvand(b1, b2))
      !! (b1 >= 11100000)
      !! (b1 <= 11200000)
      ??? == ProverStatus.Sat
    }} catch {
      case t : Throwable => { t.printStackTrace; throw t }
    }
  }

  property("bvor1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val b1 = createConstant("b1", UnsignedBVSort(8))
      val b2 = createConstant("b2", UnsignedBVSort(8))
      val b3 = createConstant("b3", UnsignedBVSort(8))
      
      !! (b3 === bvor(b1, b2))
      assert(??? == ProverStatus.Sat)

      !! (b1 =/= bv(8, 0))
      ?? (b3 =/= bv(8, 0))
      ??? == ProverStatus.Valid
    }
  }

  property("bvand_or") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val w = 4
      val b1 = createConstant("b1", UnsignedBVSort(w))
      val b2 = createConstant("b2", UnsignedBVSort(w))
      val b3 = createConstant("b3", UnsignedBVSort(w))
      val x  = createConstant("x", UnsignedBVSort(w))
      val y  = createConstant("y", UnsignedBVSort(w))
      
      // TODO: currently very slow. We need to split the diseqeuality?
      ?? (bvand(b1, bvor(b2, b3)) === bvor(bvand(b1, b2), bvand(b1, b3)))
      ??? == ProverStatus.Valid
    }
  }

  property("bvand_or2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val w = 8
      val b1 = createConstant("b1", UnsignedBVSort(w))
      val b2 = createConstant("b2", UnsignedBVSort(w))
      val b3 = createConstant("b3", UnsignedBVSort(w))
      val x  = createConstant("x", UnsignedBVSort(w))
      val y  = createConstant("y", UnsignedBVSort(w))
      
      !! (x === bvand(b1, bvor(b2, b3)))
      !! (y === bvor(bvand(b1, b2), bvand(b1, b3)))

      ?? (and((0 until w).map(n => (extract(n, n, x) === extract(n, n, y)))))

      ??? == ProverStatus.Valid
    }
  }

}

class TestExtract extends Properties("TestExtract") {
  import IExpression._
  import ModuloArithmetic._

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
        ??? == ProverStatus.Sat
      }
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
        ??? == ProverStatus.Unsat
      }
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
        ??? == ProverStatus.Unsat
      }
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
        ??? == ProverStatus.Sat
      }
    }
  }

  property("extract7") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val y = createConstant("y")
      val z = createConstant("z")

      scope {
        !! (y >= 0)
        !! (y < 256)
        !! (extract(7, 0, y) === z)
        assert(??? == ProverStatus.Sat)
      }

      scope {
        !! (y >= -1000)
        !! (y < -900)
        !! (extract(7, 0, y) === z)
        assert(??? == ProverStatus.Sat)
        !! (z === 150)
        assert(??? == ProverStatus.Unsat)
      }

      true
    }
  }

  property("extract8") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val y = createConstant("y", UnsignedBVSort(8))
      val z = createConstant("z", UnsignedBVSort(8))

      !! (extract(7, 4, y) === extract(3, 0, y))
      !! (extract(5, 2, y) === 10)
      ?? (y === 170)
      ??? == ProverStatus.Valid
    }
  }

  property("extract9") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x = createConstant("x", UnsignedBVSort(32))

      ?? ((extract(31, 1, x) === extract(30, 0, x)) <=> ((x === 0) | (x === pow2MinusOne(32))))
      ??? == ProverStatus.Valid
    }
  }

  property("extract10") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x = createConstant("x", UnsignedBVSort(32))
      val y = createConstant("y", UnsignedBVSort(16))
      val z1 = createConstant("z1", UnsignedBVSort(5))
      val z2 = createConstant("z2", UnsignedBVSort(5))

      !! (x > 10)
      !! (y === extract(15, 0, x))
      !! (z1 === extract(7, 3, y))
      !! (z2 === extract(14, 10, y))
      !! (z1 < z2)

      ??? == ProverStatus.Sat
    }
  }

  property("extract11") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x = createConstant("x", UnsignedBVSort(32))
      val y = createConstant("y", UnsignedBVSort(16))
      val z1 = createConstant("z1", UnsignedBVSort(8))
      val z2 = createConstant("z2", UnsignedBVSort(8))

      !! (x > 10)
      !! (y === extract(31, 16, x))
      !! (z1 === extract(7, 0, y))
      !! (z2 === extract(15, 8, y))
      !! (z1 < z2)

      ??? == ProverStatus.Sat
    }
  }

  property("extract12") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x = createConstant("x")

      ?? (extract(3, 2, -x) === 3 - extract(3, 2, 15 + x))
      ??? == ProverStatus.Valid
    }
  }
}
