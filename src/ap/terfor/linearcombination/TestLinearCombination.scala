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

package ap.terfor.linearcombination;

import ap.terfor._
import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.basetypes.IdealInt

class TestLinearCombination(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testLC1" => testLC1
      case "testLCFlatten" => testLCFlatten
      case "testLCAddition1" => testLCAddition1
      case "testLCAddition2" => testLCAddition2
      case "testLCAddition3" => testLCAddition3
    }
  }

  private val consts = for (i <- Array.range(0, 20)) yield new ConstantTerm("c" + i)
  private val constsAndOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  private val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c))

  private def coeffSum(searched : Term,
                       pairs : Iterable[(IdealInt, Term)]) : IdealInt =
    coeffSum(searched, pairs.iterator)

  private def coeffSum(searched : Term, pairs : LinearCombination) : IdealInt =
    coeffSum(searched, pairs.pairIterator)

  private def coeffSum(searched : Term,
                       pairs : Iterator[(IdealInt, Term)]) : IdealInt =
    IdealInt.sum(for ((c, t) <- pairs) yield {
                 t match {
                 case `searched` => c
                 case t : LinearCombination => c * coeffSum(searched, t)
                 case _ => IdealInt.ZERO
                 }})
  
  private def randomInput(len : Int) = for (i <- PlainRange(0, len))
                                       yield (IdealInt(Debug.random(-20, 20)),
                                              constsAndOne(Debug.random(0, constsAndOne.size)))
             
  /**
   * Creation and re-ordering of linear combinations
   */
  def testLC1 = {
    for (len <- PlainRange(20)) {
      val input = randomInput(len)
                          
      val lc1 = LinearCombination(input, to)       
      val lc2 = LinearCombination(input, toRev)
                    
      assertEquals(lc1.sortBy(toRev), lc2)
      assertEquals(lc1, lc2.sortBy(to))

      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield coeffSum(c, lc1) == coeffSum(c, input) &&
                                    coeffSum(c, lc2) == coeffSum(c, input) &&
                                    (lc1 get c) == coeffSum(c, input) &&
                                    (lc2 get c) == coeffSum(c, input)))
    }
  }
  
  /**
   * Flattening nested linear combinations during creation
   */
  def testLCFlatten = {
    for (len <- PlainRange(20)) {
      val input = for (i <- PlainRange(len)) yield {
                    (IdealInt(Debug.random(-20, 20)),
                     if (Debug.random(0,3) == 0)
                       LinearCombination(randomInput(Debug.random(0, 20)), to)
                     else
                       constsAndOne(Debug.random(0, constsAndOne.size)))
                  }
      
      val lc1 = LinearCombination(input, to)       
      val lc2 = LinearCombination(input, toRev)

      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield (lc1 get c) == coeffSum(c, input) &&
                                    (lc2 get c) == coeffSum(c, input)))
    }
  }

  /**
   * Addition of two linear combinations (with coefficients 1) using the
   * <code>LCBlender</code>
   */
  def testLCAddition1 = {
    for (len <- PlainRange(20)) {
      val lc1 = LinearCombination(randomInput(len), to)
      val lc2 = LinearCombination(randomInput(Debug.random(0, 20)), to)
      
      val blender = new LCBlender(to)
      
      blender ++= List((IdealInt.ONE, lc1), (IdealInt.ONE, lc2))
      blender.dropAll

      val res = blender.result
      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield (lc1 get c) + (lc2 get c) == (res get c)))
    }    
  }

  /**
   * Addition of a set of linear combinations (with arbitrary coefficients)
   * using the <code>LCBlender</code> and <code>LinearCombination.sum</code>
   */
  def testLCAddition2 = {
    for (len <- PlainRange(0, 10); lcNum <- PlainRange(5)) {
      val lcs = (for (lcLen <- Debug.randoms(0, len+1))
                 yield LinearCombination(randomInput(lcLen), to))
                .take(lcNum).toList
      val coeffs = (for (i <- Debug.randoms(-20, 20)) yield IdealInt(i))
                   .take(lcNum).toList 
      
      val blender = new LCBlender(to)
      
      blender ++= (coeffs zip lcs)
      blender.dropAll

      val res = blender.result
      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield IdealInt.sum(for ((coeff, lc) <- (coeffs zip lcs))
                                                 yield coeff * (lc get c)) ==
                                    (res get c)))

      assertEquals(res, LinearCombination.sum(coeffs zip lcs, to))
    }    
  }

  /**
   * Addition of two linear combinations (with coefficients 1) using the
   * <code>LCBlender</code>, this time with delayed adding of the linear
   * combinations to the blender
   */
  def testLCAddition3 = {
    for (len <- PlainRange(20)) {
      val lc1 = LinearCombination(randomInput(len), to)
      val lc2 = LinearCombination(randomInput(Debug.random(4, 6)), to)
      
      val blender = new LCBlender(to)
      
      blender += (IdealInt.ONE, lc1)
      
      while (blender.hasNext && to.compare(blender.peekNext _2, lc2.leadingTerm) > 0)
        blender.next
      blender += (IdealInt.ONE, lc2)
      blender.dropAll

      val res = blender.result
      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield (lc1 get c) + (lc2 get c) == (res get c)))
    }    
  }

}
