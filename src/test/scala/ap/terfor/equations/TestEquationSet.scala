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

package ap.terfor.equations;

import scala.collection.immutable.HashMap

import ap.terfor._
import ap.util.{Debug, Logic, PlainRange, FilterIt, Seqs}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination

import org.scalacheck.Properties
import ap.util.Prop._

class TestEquationSet extends Properties("TestEquationSet") {

  Debug.enableAllAssertions(true)

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsAndOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  private val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c))
  
  private def randomInput(len : Int) = for (i <- PlainRange(0, len))
                                       yield (IdealInt(Debug.random(-20, 20)),
                                              constsAndOne(Debug.random(0, constsAndOne.size)))

  private def randomLC(len : Int) = LinearCombination(randomInput(len), to)

  private var smallConstCounter : Int = 0

  private def solve(eqs : EquationConj, order : TermOrder)
                                                : (EquationConj, TermOrder) = {
    val (resEqs, resOrder) =
      new ColumnSolver (eqs, ComputationLogger.NonLogger, order) {
        protected def isSolvableEq(lc : LinearCombination, order : TermOrder) =
          if (lc.leadingCoeff.isOne) {
            None
          } else {
            val smallConst = new ConstantTerm("sc" + smallConstCounter)
            smallConstCounter = smallConstCounter + 1
            val extendedOrder = order.extend(smallConst, order.orderedConstants)
            Some((smallConst, lc.reduceWithLeadingCoeff, extendedOrder))            
          }
      }.result
    
    assertTrue(resEqs.isTrue ||
               Logic.forall(for (lc <- resEqs.iterator)
                            yield (lc.leadingCoeff.isOne)))
    (resEqs, resOrder)
  }
  
  /**
   * Solve randomly generated systems/conjunctions of linear equations
   * through row and column operations
   */
  property("testConj1") = {
    for (eqNum <- PlainRange(10); _ <- PlainRange(10)) {
//      println(eqNum)
      val input = (for (len <- Debug.randoms(0, 8)) yield randomLC(len))
                  .take(eqNum).toList
      val eqConj = EquationConj(input, to)
      val eqConjRev = EquationConj(for (lc <- input) yield lc.sortBy(toRev), toRev)
      
      // test whether the solved system of equations implies the original
      // equations
      assertTrue(eqConj.isFalse ||
                 { val reducer = ReduceWithEqs(eqConj, to)
                   Logic.forall(for (lc <- input.iterator)
                                yield reducer(lc).isZero) })
      
      val (sEqConj, sTo) = solve(eqConj, to)
      val (sEqConjRev, sToRev) = solve(eqConjRev, toRev)
      
      assertEquals(sEqConj.isFalse, sEqConjRev.isFalse)
      assertTrue(sEqConjRev.isFalse ||
                 { val reducer = ReduceWithEqs(sEqConjRev, sToRev)
                   Logic.forall(for (lc <- eqConj.iterator)
                                yield reducer(lc.sortBy(toRev)).isZero) })
      assertTrue(sEqConj.isFalse ||
                 { val reducer = ReduceWithEqs(sEqConj, sTo)
                   Logic.forall(for (lc <- eqConjRev.iterator)
                                yield reducer(lc.sortBy(to)).isZero) })
    }

    true
  }

  /**
   * Solve the individual linear equations of a randomly generated disjunction of
   * equations through row and column operations
   */
  property("testNegConj1") = {
    for (eqNum <- PlainRange(10); _ <- PlainRange(10)) {
      val input = (for (len <- Debug.randoms(0, 8)) yield randomLC(len))
                  .take(eqNum).toList
      val eqDisj = NegEquationConj(input, to)
      val eqDisjRev = NegEquationConj(for (lc <- input) yield lc.sortBy(toRev), toRev)

      assertEquals(eqDisj.sortBy(toRev), eqDisjRev)
      assertEquals(eqDisj, eqDisjRev.sortBy(to))
      
      for (lc <- eqDisj) {
        val asConj = EquationConj(lc, to)
        val (sConj, sTo) = solve(asConj, to)
        val reducer = ReduceWithEqs(sConj, sTo)
        assertTrue(reducer(eqDisj).isFalse)
        assertTrue(Logic.exists(for (lhs <- input.iterator)
                                yield reducer(lhs).isZero))
      }
    }

    true
  }
    
  /**
   * Test the reduction of arbitrary linear combinations with arbitrary
   * equations that have 1 as leading coefficient
   */
  property("testReduceWithEqs1") = {
    def randomLCUnitLeading(len : Int) : LinearCombination = {
      while (true) {
        val res = randomLC(len)
        if (!res.isZero && res.leadingCoeff.isOne &&
            res.leadingTerm.isInstanceOf[ConstantTerm])
          return res
      }
      throw new Error // never reached
    }
    
    for (eqsNum <- PlainRange(10); _ <- PlainRange(10)) {
      val eqsMap = HashMap.empty ++ (for (len <- Debug.randoms(1, 5))
                                     yield { val lc = randomLCUnitLeading(len); 
                                             (lc.leadingTerm, lc) }).take(eqsNum)
      val toBeReduced = randomLC(Debug.random(0, 10))
      val reduced = ReduceWithEqs(eqsMap, to)(toBeReduced)
      
      assertTrue(Logic.forall(for (t <- eqsMap.keysIterator)
                              yield reduced.get(t).isZero))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }

    true
  }

  /**
   * Test the reduction with linear combinations of the form <code>c3 - 1</code>
   */
  property("testReduceWithEqs2") = {
    for (eqsNum <- PlainRange(10); _ <- PlainRange(10)) {
      val eqsMap = HashMap.empty ++
        (for (i <- FilterIt(Debug.randoms(0, constsAndOne.size),
                            (i:Int) => constsAndOne(i).isInstanceOf[ConstantTerm]))
         yield (constsAndOne(i),
                LinearCombination(constsAndOne(i), to) + IdealInt.MINUS_ONE))
        .take(eqsNum)

      val toBeReduced = randomLC(Debug.random(0, 10))
      val reduced = ReduceWithEqs(eqsMap, to)(toBeReduced)

      assertEquals(reduced.constant,
                   IdealInt.sum(for (t <- eqsMap.keySet.toList)
                                yield toBeReduced.get(t)) + toBeReduced.constant)
      assertTrue(Logic.forall(
          for (t <- FilterIt(constsAndOne.iterator,
                             (t:Term) => t.isInstanceOf[ConstantTerm] &&
                                         !(eqsMap.keySet contains t)))
          yield reduced.get(t) == toBeReduced.get(t)))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }

    true
  }

  /**
   * Test the reduction of arbitrary linear combinations with arbitrary
   * equations (that do not have 0 both as left-hand- and right-hand-side)
   */
  property("testReduceWithEqs3") = {
    def randomLCNonZero(len : Int) : LinearCombination = {
      while (true) {
        val res = randomLC(len)
        if (!res.isZero && res.leadingTerm != OneTerm) return res
      }
      throw new Error // never reached
    }

    for (eqsNum <- PlainRange(10); _ <- PlainRange(10)) {
      val eqsMap = HashMap.empty ++ (for (len <- Debug.randoms(1, 5))
                                     yield { val lc = randomLCNonZero(len); 
                                             (lc.leadingTerm, lc) }).take(eqsNum)
      val toBeReduced = randomLC(Debug.random(0, 10))
      val reduced = ReduceWithEqs(eqsMap, to)(toBeReduced)
         
      assertTrue(Logic.forall(for (lc <- eqsMap.valuesIterator)
                              yield (reduced.get(lc.leadingTerm)
                                     isAbsMinMod lc.leadingCoeff)))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }

    true
  }

  /**
   * Test the reduction of equation conjunctions and disjunctions with arbitrary
   * equations (that do not have 0 both as left-hand- and right-hand-side)
   */
  property("testReduceDisj") = {
    def randomLCNonZero(len : Int) : LinearCombination = {
      while (true) {
        val res = randomLC(len)
        if (!res.isZero && res.leadingTerm != OneTerm) return res
      }
      throw new Error // never reached
    }

    for (eqsNum   <- PlainRange(10);
         disjSize <- PlainRange(5);
         _        <- PlainRange(50)) {
      val eqsMap = HashMap.empty ++ (for (len <- Debug.randoms(1, 5))
                                     yield { val lc = randomLCNonZero(len); 
                                             (lc.leadingTerm, lc) }).take(eqsNum)
      val input = (for (len <- Debug.randoms(0, 10))
                   yield randomLC(len)).take(disjSize)
      val toBeReduced = NegEquationConj(input, to)
      val toBeReduced2 = EquationConj(input, to)
      val reduced = ReduceWithEqs(eqsMap, to)(toBeReduced)
      val reduced2 = ReduceWithEqs(eqsMap, to)(toBeReduced2)

      assertTrue(toBeReduced.size != 1 ||
                 Logic.forall(for (lc <- reduced.iterator)
                              yield (to.compare(toBeReduced(0), lc) >= 0)))
      assertTrue(toBeReduced2.size != 1 ||
                 Logic.forall(for (lc <- reduced2.iterator)
                              yield (to.compare(toBeReduced2(0), lc) >= 0)))
      assertTrue(reduced2.isFalse ||
                 Logic.forall(for (lc <- reduced2.iterator)
                              yield !(eqsMap contains lc.leadingTerm)))

      val unitConsts =
        (for (c <- eqsMap.keysIterator;
              if c.isInstanceOf[ConstantTerm];
              if eqsMap(c).leadingCoeff.isUnit)
         yield c.asInstanceOf[ConstantTerm]).toSet

      assertTrue(Seqs.disjoint(unitConsts, reduced.constants))
      assertTrue(Seqs.disjoint(unitConsts, reduced2.constants))

      assertTrue((1 until reduced2.size).forall {
                   i => 
                   !reduced2(i).leadingCoeff.isUnit ||
                   (0 until i).forall {
                     j =>
                     !reduced2(j).constants.contains(
                       reduced2(i).leadingTerm.asInstanceOf[ConstantTerm])
                   }
                 })
    }

    true
  }
}
