/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.TerForConvenience

object SimpleAPITest2 extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import TerForConvenience._
  import SimpleAPI.ProverStatus

  def part(str : String) = {
    println
    println("-- " + str)
  }
  
  import p._

  part("Declaration of symbols")

  val c = createConstantRaw("c")
  val d = createConstantRaw("d")
  val r = createRelation("r", 0)
  val s = createRelation("s", 0)
  val v = createRelation("v", 0)

  println(p???) // no assertions, Sat
  
  part("Adding some assertions (uses methods from TerForConvenience._)")
  
  scope {
    implicit val o = order

    addAssertion(r & (c === d + 15))
    addAssertion(d >= 100)
    addAssertion(r ==> s)
    println(???) // still Sat

    p.scope {
      addAssertion(s ==> c <= -100)
      println(p???) // Unsat
    }
  
    println(p???) // Sat again
  }
  
  p.shutDown
}
