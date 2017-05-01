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
                                          ADTSort(1)))))

  val Seq(colour, colour_list)                    = colADT.sorts
  val Seq(red, blue, green, nil, cons)            = colADT.constructors
  val Seq(_,   _,    _,     _,   Seq(head, tail)) = colADT.selectors

  println(colADT.witnesses)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val x, y, z, a, b = createConstant

    {
    import IExpression._

    println("Test 1")
    scope {
      !! (cons(x, cons(y, nil())) === z)
      !! (head(z) === red())

      println(expect(???, ProverStatus.Sat))
      println(partialModel)
    }

    println("Test 2")
    scope {
      !! (cons(x, y) === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 3")
    scope {
      !! (colADT.hasCtor(x, 4))
      !! (x === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 4")
    scope {
      !! (colADT.hasCtor(x, 4))
      ?? (x === cons(head(x), tail(x)))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 5")
    scope {
      !! (cons(x, y) === cons(a, b))
      ?? (y === b)
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 10")
    scope {
      !! (cons(x, cons(y, z)) === z)
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 11")
    scope {
      val d = createConstant(colour)
      ?? (d === red() | d === blue() | d === green())
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 12")
    scope {
      val d = createConstant(colour)
      ?? (d === red() | d === blue())
      println(expect(???, ProverStatus.Invalid))
      println(partialModel)
      println(eval(d))
      implicit val _ = decoderContext
      println(colour asTerm eval(d))
    }

    println("Test 13")
    scope {
      val d = createConstant(colour)
      !! (d =/= red() & d =/= blue())
      ?? (d === green())
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 14")
    scope {
      val d = createConstant(colour)
      !! (d =/= red() & d =/= blue())
      ?? (d === green())
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 15")
    scope {
      ?? (colADT.hasCtor(x, 0) | colADT.hasCtor(x, 1) | colADT.hasCtor(x, 2))
      println(expect(???, ProverStatus.Invalid))
    }

    println("Test 15b")
    scope {
      val d = createConstant(colour)
      ?? (colADT.hasCtor(d, 0) | colADT.hasCtor(d, 1) | colADT.hasCtor(d, 2))
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 16")
    scope {
      !! (x === cons(y, z) | x === cons(a, b))
      ?? (x =/= nil())
      println(expect(???, ProverStatus.Valid))
    }

    println("Test 17")
    scope {
      !! (x =/= nil())
      !! (x =/= cons(head(x), tail(x)))
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 18")
    scope {
      val d = createConstant(colour)
      val e = createConstant(colour_list)
      !! (e =/= cons(red(), nil()))
      !! (e =/= cons(blue(), nil()))
      !! (e === cons(d, nil()))
      println(expect(???, ProverStatus.Sat))

      implicit val _ = decoderContext
      println(colour asTerm eval(d))
      println(colour_list asTerm eval(e))

      !! (e =/= cons(green(), nil()))
      println(expect(???, ProverStatus.Unsat))
    }

    println("Test 19")
    scope {
      val d = createConstant(colour)
      val e = createConstant(colour_list)
      !! (e =/= cons(red(), nil()))
      !! (e =/= cons(blue(), nil()))
      !! (e === cons(d, nil()))
      println(expect(???, ProverStatus.Sat))

      println(evalToTerm(d))
      println(evalToTerm(e))

      scope {
        !! (e =/= cons(green(), nil()))
        println(expect(???, ProverStatus.Unsat))
      }

      println(expect(???, ProverStatus.Sat))
      val model = partialModel
      println(model evalToTerm d)
      println(model evalToTerm e)
    }

    println("Test 20")
    scope {
      val f = createFunction("f", List(colour), colour_list)

      !! (f(green()) === nil())
      !! (f(red()) === cons(blue(), nil()))

      println(expect(???, ProverStatus.Sat))
      val model = partialModel

      println(model evalToTerm f(green()))
      println(model evalToTerm f(red()))
      println(model evalToTerm f(blue()))
    }

    println("Test 21")
    scope {
      val f = createFunction("f", List(colour_list), colour)

      !! (f(nil()) === green())
      !! (f(cons(green(), nil())) === blue())
      !! (f(cons(blue(), nil())) =/= red())

      println(expect(???, ProverStatus.Sat))
      val model = partialModel

      println(model evalToTerm f(nil()))
      println(model evalToTerm f(cons(green(), nil())))
      println(model evalToTerm f(cons(blue(), nil())))
      println(model evalToTerm f(cons(red(), nil())))
    }
    }

    println("Test 30")
    scope {
      addTheory(colADT)
      import TerForConvenience._
      implicit val _ = order
      val IConstant(xc) = x
      val IConstant(yc) = y
      val IConstant(zc) = z
      val IConstant(ac) = a
      addAssertion(colADT.constructorPreds(4)(List(l(yc), l(zc), l(xc))) |
                   colADT.constructorPreds(4)(List(l(ac), l(zc), l(xc))))
      scope {
        ?? (colADT.hasCtor(x, 4))
        println(expect(???, ProverStatus.Valid))
      }
      scope {
        ?? (colADT.hasCtor(x, 3))
        println(expect(???, ProverStatus.Invalid))
      }
    }
  }
//}