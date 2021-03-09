/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
