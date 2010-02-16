/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.basetypes;

import ap.util.{Debug, APTestCase, PlainRange, FilterIt}

class TestIdealInt(n : String) extends APTestCase(n) {
  
  def runTest = {
    n match {
      case "testDiv" => testDiv
      case "testReduceAbs" => testReduceAbs
      case "testGcdAndCofactors1" => testGcdAndCofactors1
      case "testGcdAndCofactorsSeq" => testGcdAndCofactorsSeq
      case "testGcdSeq" => testGcdSeq
    }
  }
  
  private def testDiv = {
    for (a <- Debug.randoms(-20, 20).take(50);
         b <- FilterIt(Debug.randoms(-20, 20), (b:Int) => b != 0).take(20)) {
      val ia = IdealInt(a)
      val ib = IdealInt(b)
      ia /% ib
      assertEquals(ia, (ia / ib) * ib + (ia % ib))
      assertTrue((ia % ib).signum >= 0 && (ia % ib) < b.abs)
    }
  }

  private def testReduceAbs = {
    for (a <- Debug.randoms(-20, 20).take(50);
         b <- FilterIt(Debug.randoms(-20, 20), (b:Int) => b != 0).take(20)) {
      val ia = IdealInt(a)
      val ib = IdealInt(b)
      ia reduceAbs ib
    }
  }

  private def testGcdAndCofactors1 = {
    for (a <- Debug.randoms(-20, 20).take(50);
         b <- Debug.randoms(-20, 20).take(20))
      IdealInt.gcdAndCofactors(a, b)

    for (a <- Debug.randoms(-2000000, 2000000).take(50);
         b <- Debug.randoms(-2000000, 2000000).take(20))
      IdealInt.gcdAndCofactors(a, b)
  }

  private def testGcdAndCofactorsSeq = {
    for (length <- PlainRange(6); _ <- PlainRange(10)) {
      val input = (for (x <- Debug.randoms(-20, 20).take(length))
                   yield IdealInt(x)).toList
//      println(input)
//      val (gcd, cof) = 
        IdealInt.gcdAndCofactors(input)
//      println(gcd)
//      for (x <- cof) print("" + x + " ")
//      println
    }
  }
  
  private def testGcdSeq = {
    for (length <- PlainRange(6); _ <- PlainRange(10)) {
      val input = (for (x <- Debug.randoms(-20, 20).take(length))
                   yield IdealInt(x)).toList
//      println(input)
//      val gcd = 
        IdealInt.gcd(input)
//      println(gcd)
//      for (x <- cof) print("" + x + " ")
//      println
    }
  }
}
