/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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

// package ap.theories.rationals

import ap.parser._
import ap.SimpleAPI

object TestRat extends App {

  def part(str : String) = {
    println
    println("-- " + str)
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import Rationals._
    import IExpression._

    println(zero)
    println(one)

    val x = createConstant("x", dom)
    val y = createConstant("y", dom)

    scope {
      part("Test 1")
      println(mul(frac(1, 3), frac(1, 4)))

      !! (x === mul(frac(1, 3), frac(1, 4)))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 2")
      !! (plus(frac(1, 10), x) === plus(y, int2ring(10)))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 3")
      !! (times(5, x) === int2ring(3))
      println(???)
      println(partialModel)

      !! (mul(x, y) === one)
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 4")
      !! (times(5, x) === times(7, y))
      !! (x =/= zero)
      ?? (x =/= y)
      println(???)
    }

    scope {
      part("Test 5")
      !! (times(5, x) === plus(times(7, y), int2ring(3)))
      !! (x =/= zero)
      ?? (x =/= y)
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 6")
      !! (mul(x, x) === frac(16, 9))
      println(???)
      println(partialModel)
      println(evalToTerm(x))
    }

    scope {
      part("Test 7")
      !! (y =/= zero & y =/= one)
      !! (div(x, y) === int2ring(10))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 8")
      !! (lt(zero, y) & lt(y, one))
      !! (div(x, y) === int2ring(10))
      println(???)
      println(partialModel)
    }

    scope {
      part("Test 9")
      !! (y =/= zero)
      !! (div(x, y) === int2ring(11))
      !! (lt(x, zero))
      println(???)
      println(partialModel)
    }
  }

}
