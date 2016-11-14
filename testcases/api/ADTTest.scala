/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016 Philipp Ruemmer <ph_r@gmx.net>
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

  import ap.SimpleAPI
  import ap.terfor.TerForConvenience
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ADT
  import ADT._
  import ap.util.Debug

  Debug enableAllAssertions true

  val listADT =
    new ADT (List("list"),
             List(("nil",  CtorSignature(List(), ADTSort(0))),
                  ("cons", CtorSignature(List(("head", IntSort),
                                              ("tail", ADTSort(0))),
                  ADTSort(0)))))

  val Seq(nil, cons) = listADT.constructors
  val Seq(_, Seq(head, tail)) = listADT.selectors

  println(listADT.witnesses)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    def expect[A](x : A, expected : A) : A = {
      assert(x == expected, "expected: " + expected + ", got: " + x)
      x
    }

    val x, y, z, a, b = createConstant

    {
    import IExpression._
    scope {
      !! (cons(x, cons(y, nil())) === z)
      !! (head(z) === 42)

      println(expect(???, ProverStatus.Sat))
      println(partialModel)
    }

    scope {
      !! (cons(x, y) === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      !! (listADT.hasCtor(x, 1))
      !! (x === nil())
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      !! (listADT.hasCtor(x, 1))
      ?? (x === cons(head(x), tail(x)))
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (cons(x, y) === cons(a, b))
      ?? (y === b)
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (cons(x, cons(y, z)) === z)
      println(expect(???, ProverStatus.Unsat))
    }

    scope {
      ?? (listADT.hasCtor(x, 0) | listADT.hasCtor(x, 1))
      println(expect(???, ProverStatus.Valid))
    }

    scope {
      !! (x === cons(y, z) | x === cons(a, b))
      ?? (x =/= nil())
      println(expect(???, ProverStatus.Valid))
    }
    }

    scope {
      addTheory(listADT)
      import TerForConvenience._
      implicit val _ = order
      val IConstant(xc) = x
      val IConstant(yc) = y
      val IConstant(zc) = z
      val IConstant(ac) = a
      addAssertion(listADT.constructorPreds(1)(List(l(yc), l(zc), l(xc))) |
                   listADT.constructorPreds(1)(List(l(ac), l(zc), l(xc))))
      scope {
        ?? (listADT.hasCtor(x, 1))
        println(expect(???, ProverStatus.Valid))
      }
      scope {
        ?? (listADT.hasCtor(x, 0))
        println(expect(???, ProverStatus.Invalid))
      }
    }
  }
