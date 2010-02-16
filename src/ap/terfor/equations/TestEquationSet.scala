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

package ap.terfor.equations;

import scala.collection.immutable.HashMap

import ap.util.{Debug, Logic, APTestCase, PlainRange, FilterIt}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination

class TestEquationSet(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testConj1" => testConj1
      case "testNegConj1" => testNegConj1
      case "testReduceWithEqs1" => testReduceWithEqs1
      case "testReduceWithEqs2" => testReduceWithEqs2
      case "testReduceWithEqs3" => testReduceWithEqs3
      case "testReduceDisj" => testReduceDisj
    }
  }

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsAndOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c, Set.empty))
  private val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c, Set.empty))
  
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
               Logic.forall(for (lc <- resEqs.elements)
                            yield (lc.leadingCoeff.isOne)))
    (resEqs, resOrder)
  }
  
  /**
   * Solve randomly generated systems/conjunctions of linear equations
   * through row and column operations
   */
  def testConj1 = {
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
                   Logic.forall(for (lc <- input.elements)
                                yield reducer(lc).isZero) })
      
      val (sEqConj, sTo) = solve(eqConj, to)
      val (sEqConjRev, sToRev) = solve(eqConjRev, toRev)
      
      assertEquals(sEqConj.isFalse, sEqConjRev.isFalse)
      assertTrue(sEqConjRev.isFalse ||
                 { val reducer = ReduceWithEqs(sEqConjRev, sToRev)
                   Logic.forall(for (lc <- eqConj.elements)
                                yield reducer(lc.sortBy(toRev)).isZero) })
      assertTrue(sEqConj.isFalse ||
                 { val reducer = ReduceWithEqs(sEqConj, sTo)
                   Logic.forall(for (lc <- eqConjRev.elements)
                                yield reducer(lc.sortBy(to)).isZero) })
    }
  }

  /**
   * Solve the individual linear equations of a randomly generated disjunction of
   * equations through row and column operations
   */
  def testNegConj1 = {
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
        assertTrue(Logic.exists(for (lhs <- input.elements)
                                yield reducer(lhs).isZero))
      }
    }
  }
    
  /**
   * Test the reduction of arbitrary linear combinations with arbitrary
   * equations that have 1 as leading coefficient
   */
  def testReduceWithEqs1 = {
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
      
      assertTrue(Logic.forall(for (t <- eqsMap.keys)
                              yield reduced.get(t).isZero))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }
  }

  /**
   * Test the reduction with linear combinations of the form <code>c3 - 1</code>
   */
  def testReduceWithEqs2 = {
    for (eqsNum <- PlainRange(10); _ <- PlainRange(10)) {
      val eqsMap = HashMap.empty ++
        (for (i <- FilterIt(Debug.randoms(0, constsAndOne.size),
                            (i:Int) => constsAndOne(i).isInstanceOf[ConstantTerm]))
         yield (constsAndOne(i),
                LinearCombination(Array((IdealInt.ONE, constsAndOne(i)),
                                        (IdealInt.MINUS_ONE, OneTerm)),
                                  to)))
        .take(eqsNum)

      val toBeReduced = randomLC(Debug.random(0, 10))
      val reduced = ReduceWithEqs(eqsMap, to)(toBeReduced)

      assertEquals(reduced.constant,
                   IdealInt.sum(for (t <- eqsMap.keySet.toList)
                                yield toBeReduced.get(t)) + toBeReduced.constant)
      assertTrue(Logic.forall(
          for (t <- FilterIt(constsAndOne.elements,
                             (t:Term) => t.isInstanceOf[ConstantTerm] &&
                                         !(eqsMap.keySet contains t)))
          yield reduced.get(t) == toBeReduced.get(t)))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }
  }

  /**
   * Test the reduction of arbitrary linear combinations with arbitrary
   * equations (that do not have 0 both as left-hand- and right-hand-side)
   */
  def testReduceWithEqs3 = {
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
         
      assertTrue(Logic.forall(for (lc <- eqsMap.values)
                              yield (reduced.get(lc.leadingTerm)
                                     isAbsMinMod lc.leadingCoeff)))
      assertTrue(to.compare(toBeReduced, reduced) >= 0)
    }
  }

  /**
   * Test the reduction of equation conjunctions and disjunctions with arbitrary
   * equations (that do not have 0 both as left-hand- and right-hand-side)
   */
  def testReduceDisj = {
    def randomLCNonZero(len : Int) : LinearCombination = {
      while (true) {
        val res = randomLC(len)
        if (!res.isZero && res.leadingTerm != OneTerm) return res
      }
      throw new Error // never reached
    }

    for (eqsNum <- PlainRange(10); disjSize <- PlainRange(5); _ <- PlainRange(10)) {
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
                 Logic.forall(for (lc <- reduced.elements)
                              yield (to.compare(toBeReduced(0), lc) >= 0)))
      assertTrue(toBeReduced2.size != 1 ||
                 Logic.forall(for (lc <- reduced2.elements)
                              yield (to.compare(toBeReduced2(0), lc) >= 0)))

      assertTrue(reduced2.isFalse ||
                 Logic.forall(for (lc <- reduced2.elements)
                              yield !(eqsMap contains lc.leadingTerm)))
    }
  }
}
