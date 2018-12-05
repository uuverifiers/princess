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

// Bit-vector evaluation

  import ap.SimpleAPI
  import SimpleAPI.ProverStatus
  import ap.parser._
  import ap.theories.ModuloArithmetic
  import ap.util.Debug

  Debug enableAllAssertions true

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    import IExpression._
    import ModuloArithmetic._

    // if the prover does not know the theory, and no theory expressions
    // have been asserted, eval can fail
    addTheory(ModuloArithmetic)

    scope {
      println(???)

      val model = partialModel

      println("1: " + (model eval 3))
      println("2: " + (model eval true))

      println("3: " + (model eval bv(4, 3)))
      println("4: " + (model evalToTerm bv(4, 3)))

      println("5: " + (evalPartial(bv(4, 3))))
      println("6: " + (evalToTerm(bv(4, 3))))
      println("7: " + (eval(bv(4, 3))))

      println("8: " + (model eval bvadd(bv(4, 3), bv(4, 1))))
      println("9: " + (model eval bvmul(bv(4, 3), bv(4, 2))))

      println("10: " + (evalPartial(bvadd(bv(4, 3), bv(4, 1)))))
      println("11: " + (evalToTerm(bvadd(bv(4, 3), bv(4, 1)))))
      println("12: " + (eval(bvadd(bv(4, 3), bv(4, 1)))))
    }

    scope {
      val x = createConstant("x", UnsignedBVSort(4))
      !! (x === bv(4, 3))

      println(???)
      val model = partialModel
      println("13: " + (model evalToTerm x))
      println("14: " + (model eval x))
      println("15: " + (evalToTerm(x)))
      println("16: " + (eval(x)))
    }

    scope {
      val x = createConstant("x", UnsignedBVSort(4))
      val f = createFunction("f", List(UnsignedBVSort(4)), UnsignedBVSort(4))
      !! (bvugt(x, bv(4, 2)))
      !! (f(x) === bv(4, 3))

      println(???)
      val model = partialModel
      println("17: " + (model evalToTerm f(x)))
      println("18: " + (model eval f(x)))
      println("19: " + (evalToTerm(f(x))))
      println("20: " + (eval(f(x))))

      println("21: " + (model evalToTerm f(bvsub(x, bv(4, 0)))))
      println("22: " + (model eval f(bvsub(x, bv(4, 0)))))
      println("23: " + (evalToTerm(f(bvsub(x, bv(4, 0))))))
      println("24: " + (eval(f(bvsub(x, bv(4, 0))))))

      println("25: " + (model eval bvult(bv(4, 0), x)))
    }

    // Test whether the SimplifyConstantSubstVisitor simplifies BV expressions
    scope {
      val x@IConstant(_x) = createConstant("x", UnsignedBVSort(4))
      val y@IConstant(_y) = createConstant("y", UnsignedBVSort(4))

      val f = bvule(bv(4, 1), bvadd(x, y))
      val g = bvadd(x, bvadd(y, bv(4, 14)))

      println("26: " + SimplifyingConstantSubstVisitor(f, Map(_x -> bv(4, 1),
                                                              _y -> bv(4, 2))))
      println("27: " + SimplifyingConstantSubstVisitor(g, Map(_x -> bv(4, 1),
                                                              _y -> bv(4, 2))))
    }
  }
