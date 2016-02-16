/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.collection.mutable.ArrayBuffer

object APTestCase {

  class TestException(msg : String) extends Exception(msg)

  class TestResult {
    val exceptions = new ArrayBuffer[Throwable]
  }

}

abstract class APTestCase(n : String) {
  
  import APTestCase._

  def runTest : Unit

  def setUp : Unit = {}
  def tearDown : Unit = {}

  def run(r: TestResult) {
    // ensure that tests are deterministic
    Debug.initRandomGen(29473878)

    setUp

    try {
      runTest
    } catch {
      case t : Throwable => r.exceptions += t
    }

    tearDown

    print(".")
  }
  
  def assertEquals(a : Any, b : Any) : Unit =
    if (!(a == b))
      throw new TestException("Expected " + a + " to be equal to " + b)

  def assertEquals(msg : String, a : Any, b : Any) : Unit =
    if (!(a == b))
      throw new TestException("Expected " + a +
                              " to be equal to " + b + ": " + msg)

  def assertTrue(b : Boolean) : Unit =
    if (!b)
      throw new TestException("Expected condition to be true")

  def assertTrue(msg : String, b : Boolean) : Unit =
    if (!b)
      throw new TestException("Expected condition to be true: " + msg)

}
