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

// Test of the different scoping methods

//package ap

//object TestFrame extends App {
  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import IExpression._
  import ap.util.Debug

  Debug enableAllAssertions true

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    scope {
      val x = createConstant("x")
      val y = createConstant("y")

      !! (x > y)
      println(expect(???, ProverStatus.Sat))

      scope {
        !! (x < y)
        println(expect(???, ProverStatus.Unsat))
      }

      scope(resetFormulas = true) {
        !! (x < y)
        println(expect(???, ProverStatus.Sat))
      }

      val f = createFunction("f", List(Sort.Integer), Sort.Integer)
      scope(resetFormulas = true) {
        !! (f(x) < 0)
        !! (all(a => f(a) > a))
        !! (y > 10)
        println(expect(???, ProverStatus.Inconclusive))
        !! (x > y)
        println(expect(???, ProverStatus.Unsat))
      }     

      // check whether asserted formulas can get in the way of
      // quantifier elimination (they shouldn't!)
      !! (x === 42)
      println(pp(simplify(ex(z => (y < z) & (z < x)))))
    }
  }
//}
