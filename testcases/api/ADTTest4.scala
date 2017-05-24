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

// Unit tests for the decision procedure for algebraic data-types

//object ADTTest extends App {
  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ADT
  import ADT._
  import ap.util.Debug

  Debug enableAllAssertions true

  val colADT =
    new ADT (List("colour", "colour_list"),
             List(("red",   CtorSignature(List(), ADTSort(0))),
                  ("blue",  CtorSignature(List(), ADTSort(0))),
                  ("green", CtorSignature(List(), ADTSort(0))),
                  ("nil",   CtorSignature(List(), ADTSort(1))),
                  ("cons",  CtorSignature(List(("head", ADTSort(0)),
                                               ("tail", ADTSort(1))),
                                          ADTSort(1)))),
             ADT.TermMeasure.Size)

  val Seq(colour, colour_list)                    = colADT.sorts
  val Seq(red, blue, green, nil, cons)            = colADT.constructors
  val Seq(_,   _,    _,     _,   Seq(head, tail)) = colADT.selectors
  val Seq(colour_size, colour_list_size)          = colADT.termSize

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val c1, c2 = createConstant(colour)
    val x, y, z = createConstant(colour_list)

    import IExpression._

    println("Test 1")
    scope {
      !! (cons(c1, cons(c2, x)) === z)
      !! (head(z) === red())

      println(expect(???, ProverStatus.Sat))
      println(evalToTerm(z))

      scope {
        !! (colour_list_size(z) === 13)

        println(expect(???, ProverStatus.Sat))
        println(evalToTerm(z))
      }

      scope {
        !! (colour_list_size(z) === 14)

        println(expect(???, ProverStatus.Unsat))
      }
    }

  }
//}