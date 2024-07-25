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

package ap.terfor;

import scala.collection.immutable.HashSet

import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.basetypes.IdealInt
import linearcombination.LinearCombination

class TestTermOrder(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testSimpleExtension" => testSimpleExtension
      case "testConditionalExtension" => testConditionalExtension
      case "testLinearCombinationComparison" => testLinearCombinationComparison
    }
  }
  
  private val consts = for (i <- Array.range(0, 20)) yield new ConstantTerm("c" + i)

  def testSimpleExtension = {
    var to = TermOrder.EMPTY
    for (c <- consts) to = to.extend(c, Set.empty)
    
    for ((i, j) <- (Debug.randoms(0, 20).take(100) zip
                    Debug.randoms(0, 20).take(100))) {
      assertEquals(Debug.signum(i compare j),
                   Debug.signum(to.compare(consts(i), consts(j))))
      assertEquals(Debug.signum(j compare i),
                   Debug.signum(to.compare(VariableTerm(i), VariableTerm(j))))
      assertTrue(to.compare(consts(i), VariableTerm(4))
                 < 0)
      assertTrue(to.compare(consts(i), OneTerm)
                 > 0)
    }
  }

  def testConditionalExtension = {
    var to = TermOrder.EMPTY
    for (c <- consts) {
      val biggerConsts = HashSet.empty ++
                         (for (i <- Debug.randoms(0, 20).take(Debug.random(0,50)))
                          yield consts(i))
      to = to.extend(c, biggerConsts - c)
    }
  }

  def testLinearCombinationComparison = {
    var to = TermOrder.EMPTY
    for (c <- consts) to = to.extend(c, Set.empty)

    val constTerms = consts ++ List(OneTerm)
  
    def randomInput = for (i <- PlainRange(10, constTerms.size))
                      yield (IdealInt(Debug.random(-3, 3)), constTerms(i))

    // not really a correct implementation, but it covers all cases that occur
    // here
    def smallerThan(lc1 : LinearCombination, lc2 : LinearCombination) : Boolean =
      Logic.exists(0, 10,
                   (i:Int) => Logic.forall(0, i,
                                           (j:Int) => lc1.getPair(j) == lc2.getPair(j)) &&
                              (to.compare(lc1 getTerm i, lc2 getTerm i) < 0 ||
                               (lc1 getTerm i) == (lc2 getTerm i) &&
                               ((lc1 getCoeff i) compareAbs (lc2 getCoeff i)) < 0))

    for (_ <- PlainRange(100)) {
      val lc1 = LinearCombination(randomInput, to)
      val lc2 = LinearCombination(randomInput, to)

      val res = to.compare(lc1, lc2)
      if (smallerThan(lc1, lc2))
        assertTrue ( res < 0 )
      else if (smallerThan(lc2, lc1))
        assertTrue ( res > 0 )
    }
  }
}
