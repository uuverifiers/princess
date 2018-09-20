/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

// Some simple API tests for strings

//package ap.theories.strings

//object TestStrings extends App {
  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.strings.SeqStringTheory
  import ap.util.Debug

  Debug enableAllAssertions true

  val stringTheory = SeqStringTheory(256)
  import stringTheory._
  import IExpression._

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x, y, z = createConstant(StringSort)
    implicit val _ = decoderContext

    scope {
      !! (x === "abc")

      println(???)
      println("x = " + evalToTerm(x))
      println("x = \"" + asString(eval(x)) + "\"")

      !! (x ++ y ++ "xyz" === z)

      println(???)
      println("y = " + evalToTerm(y))
      println("z = " + evalToTerm(z))
      println("z = \"" + asString(eval(z)) + "\"")

      !! (y =/= "")

      println(???)
      println("y = " + evalToTerm(y))
      println("z = " + evalToTerm(z))
      println("z = \"" + asString(eval(z)) + "\"")

      !! (y === z)

      println(???)
    }

    scope {
      !! (x ++ y === y ++ x)
      !! (str_len(x) === 2)
      !! (str_len(y) === 5)
      !! (x =/= "")

      println(???)
      println("x = " + evalToTerm(x))
      println("y = " + evalToTerm(y))

      ?? (str_head(x) === str_head(str_tail(x)))

      println(???)
    }
  }

//}
