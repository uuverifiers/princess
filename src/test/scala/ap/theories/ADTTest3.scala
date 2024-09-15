/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2024 Philipp Ruemmer <ph_r@gmx.net>
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


package ap.theories

//object ADTTest extends App {
  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ADT._
  import ap.util.Debug

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class ADTTest3 extends Properties("ADTTest3") with ExtraAssertions {

  val expectedOutput = """Vector(red, nil)
Test 1
Sat
{c2 -> 3, c1 -> 2, c0 -> 0, colour_list_depth(cons(green, nil)) -> 7, colour_list_depth(nil) -> 6, colour_list_depth(cons(red, cons(green, nil))) -> 8, colour_list_ctor(cons(green, nil)) -> 1, colour_list_ctor(nil) -> 0, colour_list_ctor(cons(red, cons(green, nil))) -> 1, tail(cons(green, nil)) -> nil, tail(cons(red, cons(green, nil))) -> cons(green, nil), head(cons(green, nil)) -> green, head(cons(red, cons(green, nil))) -> red, cons(green, nil) -> cons(green, nil), cons(red, cons(green, nil)) -> cons(red, cons(green, nil)), nil -> nil}
Test 2
Unsat
Test 3
Unsat
Test 4
Valid
Test 5
Valid
Test 10
Unsat
Test 11
Valid
Test 12
Invalid
{c5 -> green}
2
Some(green)
Test 13
Valid
Test 14
Valid
Test 15
Invalid
Test 15b
Valid
Test 16
Valid
Test 17
Unsat
Test 18
Sat
Some(green)
Some(cons(green, nil))
Unsat
Test 19
Sat
green
cons(green, nil)
Unsat
Sat
Some(green)
Some(cons(green, nil))
Test 20
Sat
Some(nil)
Some(cons(blue, nil))
None
Test 21
Sat
Some(green)
Some(blue)
Some(green)
None
Test 30
Valid
Invalid
Vector(red, nil)
Test 1
Sat
{c2 -> 6, c1 -> 0, c0 -> 0, colour_list_size(cons(red, nil)) -> 3, colour_list_size(nil) -> 1, colour_list_size(cons(red, cons(red, nil))) -> 5, colour_list_ctor(cons(red, nil)) -> 1, colour_list_ctor(nil) -> 0, colour_list_ctor(cons(red, cons(red, nil))) -> 1, tail(cons(red, nil)) -> nil, tail(cons(red, cons(red, nil))) -> cons(red, nil), head(cons(red, nil)) -> red, head(cons(red, cons(red, nil))) -> red, cons(red, cons(red, nil)) -> cons(red, cons(red, nil)), cons(red, nil) -> cons(red, nil), nil -> nil}
Test 2
Unsat
Test 3
Unsat
Test 4
Valid
Test 5
Valid
Test 10
Unsat
Test 11
Valid
Test 12
Invalid
{c5 -> green}
2
Some(green)
Test 13
Valid
Test 14
Valid
Test 15
Invalid
Test 15b
Valid
Test 16
Valid
Test 17
Unsat
Test 18
Sat
Some(green)
Some(cons(green, nil))
Unsat
Test 19
Sat
green
cons(green, nil)
Unsat
Sat
Some(green)
Some(cons(green, nil))
Test 20
Sat
Some(nil)
Some(cons(blue, nil))
None
Test 21
Sat
Some(green)
Some(blue)
Some(blue)
None
Test 30
Valid
Invalid
"""

  property("ADTTest3") = checkOutput(expectedOutput) {

  Debug enableAllAssertions true

  for (measure <- ADT.TermMeasure.values) {

  val colADT =
    new ADT (List("colour", "colour_list"),
             List(("red",   CtorSignature(List(), ADTSort(0))),
                  ("blue",  CtorSignature(List(), ADTSort(0))),
                  ("green", CtorSignature(List(), ADTSort(0))),
                  ("nil",   CtorSignature(List(), ADTSort(1))),
                  ("cons",  CtorSignature(List(("head", ADTSort(0)),
                                               ("tail", ADTSort(1))),
                                          ADTSort(1)))),
             measure)

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
      implicit val ctxt = decoderContext
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

      implicit val ctxt = decoderContext
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
      implicit val o = order
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
  }
}
}
