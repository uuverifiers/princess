/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2018 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

// Unit tests for bit-vectors

//package ap.theories

//object TestModuloArithmetic extends App {
  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ModuloArithmetic
  import ap.util.Debug

  Debug enableAllAssertions true

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    import IExpression._
    import ModuloArithmetic._

    val b1 = createConstant("b1", UnsignedBVSort(8))
    val b2 = createConstant("b2", UnsignedBVSort(8))
    val w1 = createConstant("w1", UnsignedBVSort(32))
    val w2 = createConstant("w2", UnsignedBVSort(32))
    val h1 = createConstant("h1", UnsignedBVSort(16))

    println("Test 1")
    scope {
      !! (bvadd(b1, b2) === bv(8, 13))
      println(expect(???, ProverStatus.Sat))
      println(partialModel)
      println("b1 = " + evalToTerm(b1))
    }

    println("Test 2")
    scope {
      !! (bvadd(w1, w2) === bv(32, 13))
      println(expect(???, ProverStatus.Sat))
      println(partialModel)
    }

    println("Test 3")
    scope {
      !! (extract(15, 8, w1) === bv(8, 42))
      !! (extract(7, 0, w1)  === bv(8, 255))
      !! (w1 === concat(h1, h1))
      println(expect(???, ProverStatus.Sat))
      println("h1 = " + evalToTerm(h1))
      !! (extract(31, 24, w1) =/= bv(8, 42))
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 4")
    scope {
      ?? (bvmul(w1, (bvadd(w1, bv(32, 1)))) === bvadd(bvmul(w1, w1), w1))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 5")
    scope {
      ?? (sign_extend(31, bv(1, 1)) === sign_extend(30, bv(2, 3)))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 6")
    scope {
      ?? (extract(31, 31, sign_extend(31, bv(1, 1))) === bv(1, 1))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 7")
    scope {
      setConstructProofs(true)
      val x = createConstant("x", UnsignedBVSort(1))
      val y = createConstant("y", UnsignedBVSort(1))
      val z = createConstant("z", UnsignedBVSort(32))
      setPartitionNumber(1)
      !! (x =/= bv(1, 0))
      setPartitionNumber(2)
      !! (z === sign_extend(31, x))
      !! (y === extract(31, 31, z))
      setPartitionNumber(3)
      !! (y === bv(1, 0))
      println(expect(???, ProverStatus.Unsat))
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }

    println("Test 8")
    scope {
      val width = 2
      val x = createConstant("x", UnsignedBVSort(width))
      val f = UnsignedBVSort(width).ex(y => bvmul(x, y) === bv(width, 1))
      println(pp(f))
      val simpF = simplify(f)
      println(pp(simpF))
      ?? (simpF <=> (extract(0, 0, x) === bv(1, 1)))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 9")
    scope {
      setConstructProofs(true)
      val width = 8

      val a = createConstant("a", UnsignedBVSort(width))
      val b = createConstant("b", UnsignedBVSort(width))
      val c = createConstant("c", UnsignedBVSort(width))

      val A = (b === bvadd(a, bv(width, 130)))
      val B = bvugt(b, a)
      val C = (c === bvadd(b, bv(width, 130)))
      val D = bvugt(c, b)

      setPartitionNumber(1)
      !! (A)
      setPartitionNumber(2)
      !! (B)
      setPartitionNumber(3)
      !! (C)
      setPartitionNumber(4)
      !! (D)

      println(expect(???, ProverStatus.Unsat))
      println(getInterpolants(List(Set(1), Set(2), Set(3), Set(4))) map (pp(_)))
    }
  }
//}