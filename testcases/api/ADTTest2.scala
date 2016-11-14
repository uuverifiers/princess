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

// Unit tests for the decision procedure for algebraic data-types,
// testing interpolation

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

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x = createConstant("x")
    val y = createConstant("y")
    val a = createConstant("a")
    val z, b, c, d = createConstant

    import IExpression._

    setConstructProofs(true)

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      setPartitionNumber(2)
      !! (x === nil())

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y > 0)
      setPartitionNumber(2)
      !! (head(x) === 0)

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y === 42)
      setPartitionNumber(2)
      !! (x === cons(a, b))
      !! (a === 43)

      println(???)
      println(getInterpolants(List(Set(1), Set(2))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(y, z))
      !! (y === 42)
      setPartitionNumber(2)
      !! (a === cons(head(x) - 1, x))
      setPartitionNumber(3)
      !! (a === cons(c, d))
      !! (c === 43)

      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === nil())
      setPartitionNumber(2)
      !! (y === nil())
      setPartitionNumber(3)
      ?? (x === y)
      
      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }

    scope {
      setPartitionNumber(1)
      !! (x === cons(1, cons(2, nil())))
      setPartitionNumber(2)
      !! (y === cons(1, cons(2, nil())))
      setPartitionNumber(3)
      ?? (x === y)
      
      println(???)
      println(getInterpolants(List(Set(1), Set(2), Set(3))))
    }
  }
