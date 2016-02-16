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

object SimpleAPITest10 extends App {

  ap.util.Debug.enableAllAssertions(true)
  val p1 = SimpleAPI.spawnWithAssertions
  val p2 = SimpleAPI.spawnWithAssertions

  import IExpression._
  import SimpleAPI.ProverStatus

  val a = p1 createBooleanVariable "a"
  val b = p1 createBooleanVariable "b"
  val o = a | b

  val ab = p1 abbrev o
  p1 !! ab
  println(p1 ???)    // Sat

  p2 addBooleanVariable a
  p2 addBooleanVariable b
  p2.addAbbrev(ab, o)

  p2 !! ab
  println(p2 ???)    // Sat

  p1.shutDown
  p2.shutDown

}