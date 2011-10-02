/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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
