/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.parser._

object SimpleAPITest7 extends App {

  ap.util.Debug.enableAllAssertions(true)
  val p1 = SimpleAPI.spawnWithAssertions
  val p2 = SimpleAPI.spawnWithAssertions

  import IExpression._
  import SimpleAPI.ProverStatus

  val f = p1.createFunction("f", 1)
  p2 addFunction f

  val x = p1.createConstant
  p2 addConstant x

  val phi =
    and(for (i <- 1 until 16) yield (f(i) === -f(i-1) + 3)) &
    (f(x) > 1) & (x >= 0 & x < 16)

  p1.scope {
    p1 !! phi
    p1 !! (f(0) === 1)
    println(p1 ???)
  }

  p2.scope {
    p2 !! phi
    p2 !! (f(0) === 0)
    println(p2 ???)
    println(p2.partialModel.eval(f(1)))
  }

  p1.shutDown
  p2.shutDown

}