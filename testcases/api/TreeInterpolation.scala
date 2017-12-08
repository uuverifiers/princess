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

// Unit test for tree interpolation functionality. Previously, when a
// formula was asserted repeatedly in a tree interpolation problem,
// sometimes incorrect interpolants were returned.

//package ap;

import ap.SimpleAPI
import ap.parser._
import ap.basetypes.Tree

//object TreeIntTest {
//  def main(args: Array[String]) =
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      setConstructProofs(true)

      val a = createConstant("a")
      val b = createConstant("b")
      val c = createConstant("c")
      val d = createConstant("d")
      val e = createConstant("e")

      val A =  a === 1
      val B =  a === b
      val R1 = b === c
      val C =  c === d + 1
      val R2 = d === e
      val D =  e === 5

      setPartitionNumber(1)
      !! (A)

      setPartitionNumber(10)
      !! (B)

      setPartitionNumber(2)
      !! (A)

      setPartitionNumber(20)
      !! (C)

      setPartitionNumber(3)
      !! (R1)

      setPartitionNumber(4)
      !! (A)

      setPartitionNumber(40)
      !! (D)

      setPartitionNumber(5)
      !! (R2)

      println(???)

      println(getUnsatCore.toList.sorted)

      getTreeInterpolant(
        Tree(Set(5),
             List(Tree(Set(3), List(
                       Tree(Set(1, 10), List()),
                       Tree(Set(2, 20), List())
                  )),
                  Tree(Set(4, 40), List())))).prettyPrint
  }
//}
