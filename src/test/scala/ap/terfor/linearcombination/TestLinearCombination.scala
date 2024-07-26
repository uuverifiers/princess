/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.linearcombination;

import ap.terfor._
import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.basetypes.IdealInt

import org.scalacheck.Properties
import ap.util.Prop._

class TestLinearCombination extends Properties("TestLinearCombination") {

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
  property("testLC1") = {
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

    true
  }
  
  /**
   * Flattening nested linear combinations during creation
   */
  property("testLCFlatten") = {
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

    true
  }

  /**
   * Addition of two linear combinations (with coefficients 1) using the
   * <code>LCBlender</code>
   */
  property("testLCAddition1") = {
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

    true
  }

  /**
   * Addition of a set of linear combinations (with arbitrary coefficients)
   * using the <code>LCBlender</code> and <code>LinearCombination.sum</code>
   */
  property("testLCAddition2") = {
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

    true
  }

  /**
   * Addition of two linear combinations (with coefficients 1) using the
   * <code>LCBlender</code>, this time with delayed adding of the linear
   * combinations to the blender
   */
  property("testLCAddition3") = {
    for (len <- PlainRange(20)) {
      val lc1 = LinearCombination(randomInput(len), to)
      val lc2 = LinearCombination(randomInput(Debug.random(4, 6)), to)
      
      val blender = new LCBlender(to)
      
      blender += (IdealInt.ONE, lc1)
      
      while (blender.hasNext && to.compare(blender.peekNext _2, lc2.leadingTerm) > 0)
        blender.next()
      blender += (IdealInt.ONE, lc2)
      blender.dropAll

      val res = blender.result
      assertTrue(Logic.forall(for (c <- constsAndOne)
                              yield (lc1 get c) + (lc2 get c) == (res get c)))
    }

    true
  }

}
