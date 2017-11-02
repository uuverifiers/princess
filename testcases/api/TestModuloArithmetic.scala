/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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
  }
//}