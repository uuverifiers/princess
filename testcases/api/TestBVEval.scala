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

    // if the prover does not know the theory, eval can fail
    addTheory(ModuloArithmetic)

    println(???)

    val model = partialModel

    println(model eval 3)
    println(model eval true)

    println(model eval bv(4, 3))
    println(model evalToTerm bv(4, 3))

    println(evalPartial(bv(4, 3)))
    println(evalToTerm(bv(4, 3)))
    println(eval(bv(4, 3)))
  }
