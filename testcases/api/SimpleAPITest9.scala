/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import ap._
import ap.parser._

object SimpleAPITest9 extends App {

  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions

  import IExpression._
  import SimpleAPI.ProverStatus
  import p._

  val x = createConstant("x")
  val y = createConstant("y")
  val z = createConstant("z")

  val t1 = abbrev(x + 2*y)

  scope {
    !! (t1 === 5)
    println(???)   // Sat
    scope {
      ?? (t1 > 0)
      println(???) // Valid
    }
    !! (x < -5)
    !! (y < 0)
    println(???)   // Unsat
  }

  scope {
    val t2 = abbrev(z + 2*x)
    !! (t1 + t2 === 3)
    println(???)   // Sat
  }

  scope {
    var f1 = abbrev(t1 > 0)
    for (_ <- 0 until 100)
      f1 = abbrev(f1 & f1)
    !! (f1)
    println(???)   // Sat
    !! (x < -5)
    !! (y < 0)
    println(???)   // Unsat
  }

  p.shutDown

}
