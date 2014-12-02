/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2014 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.theories.SimpleArray

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._

  val ar = SimpleArray(2)
  val a, b, c = createConstant
  implicit val _ = decoderContext

  scope {
    !! (b === ar.store(a, 0, 1, 2))
    !! (c === ar.store(b, 1, 2, 3))

    scope {
      println(???) // Sat
      println(ar.asMap(eval(c)).toList sortBy (_._2))

      !! (ar.select(c, 0, 2) > 0)
      println(???) // Sat
      println(ar.asMap(eval(c)).toList sortBy (_._2))

      !! (ar.select(b, 0, 2) < 0)
      println(???) // Unsat
    }

    scope {
      ?? (ar.select(c, 0, 1) > 0)
      println(???) // Valid
    }
  }

}
