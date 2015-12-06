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

package ap.terfor.inequalities;

import ap.terfor._
import ap.util.{Debug, Logic, APTestCase, PlainRange, FilterIt}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}

class TestInequalities(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testConj1" => testConj1
      case "testConj2" => testConj2
      case "testReduceWithInEqs1" => testReduceWithInEqs1
      case "testReduceWithInEqs2" => testReduceWithInEqs2
    }
  }

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsAndOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  private val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c))
  
  private def randomInput(len : Int) = for (i <- PlainRange(0, len))
                                       yield (IdealInt(Debug.random(-20, 20)),
                                              constsAndOne(Debug.random(0, constsAndOne.size)))

  private def randomLC(len : Int) = LinearCombination(randomInput(len), to)

  
  /**
   * Create random systems/conjunctions of inequalities
   */
  def testConj1 = {
    for (eqNum <- PlainRange(11); _ <- PlainRange(50)) {
      val input = (for (len <- Debug.randoms(0, 8)) yield randomLC(len))
                   .take(eqNum).toList
//                   println(input)
      val eqConj = InEqConj(input, to)
      val eqConjRev = InEqConj(for (lc <- input) yield lc.sortBy(toRev), toRev)
        
/*      println(eqConj)
      println(eqConj.geqZeroInfs)
      println(eqConj.equalityInfs)
      println("" + eqConj.geqZero.size + " " + eqConj.geqZeroInfs.size)
      println */
      
      assertTrue(eqConj.isFalse ||
                 Logic.forall(for (lc <- input.iterator)
                              yield (eqConj findLowerBound lc) match {
                                       case None => false
                                       case Some(d) => d.signum >= 0
                                     }))

      // The following does not hold in general:                               
      //      assertEquals(eqConj sortBy toRev, eqConjRev)
      
      assertEquals(InEqConj(eqConj.geqZero ++ eqConj.geqZeroInfs, to), eqConj)
     

      // test whether the solved system of equations implies the original
      // equations
/*        assertTrue(eqConj.isFalse ||
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
                                  yield reducer(lc.sortBy(to)).isZero) }) */
      }
    }

  /**
   * Create random systems/conjunctions of inequalities and their conjunction
   */
  def testConj2 = {
    for (conjNum <- PlainRange(5); _ <- PlainRange(50)) {
      val input = (for (eqNum <- Debug.randoms(0, 6)) yield
                    InEqConj((for (len <- Debug.randoms(0, 8))
                              yield randomLC(len)).take(eqNum),
                             to)
                  ).take(conjNum).toList
//      println(input)
      val eqConj = InEqConj.conj(input, to)
        
      if (input.size == 1) assertEquals(input.head, eqConj)
      
/*        println(eqConj)
        println(eqConj.geqZeroInfs)
        println(eqConj.equalityInfs)
        println("" + eqConj.geqZero.size + " " + eqConj.geqZeroInfs.size)
        println */
    }
  }

  /**
   * Create random systems/conjunctions of equations, negated equations and
   * inequalities and reduce them
   */
  def testReduceWithInEqs1 = {
    for (eqNum <- PlainRange(10); inEqNum <- PlainRange(10); _ <- PlainRange(30)) {
      val eqInput = (for (len <- Debug.randoms(0, 4)) yield randomLC(len))
                     .take(eqNum).toList
      val eqConj = EquationConj(eqInput, to)
      val negEqConj = NegEquationConj(eqInput, to)

      val inEqInput = (for (len <- Debug.randoms(0, 4)) yield randomLC(len))
                       .take(inEqNum).toList
      val inEqConj = InEqConj(inEqInput, to)

      val reducer = ReduceWithInEqs(inEqConj, to)
      
      reducer(eqConj)
      reducer(negEqConj)
    }
  }

  /**
   * Reduce inequalities using other inequalities
   */
  def testReduceWithInEqs2 = {
    for (redInEqNum <- PlainRange(10); inEqNum <- PlainRange(10); _ <- PlainRange(30)) {
      val redInput = (for (len <- Debug.randoms(0, 4)) yield randomLC(len))
                      .take(redInEqNum).toList
      val toBeReduced = InEqConj(redInput, to)

      val inEqInput = (for (len <- Debug.randoms(0, 4)) yield randomLC(len))
                       .take(inEqNum).toList
      val inEqConj = InEqConj(inEqInput, to)

      val reducer = ReduceWithInEqs(inEqConj, to)
      
      // reducing inequalities with itself produces a trivial conjunction
      assert(inEqConj.isFalse || !inEqConj.equalityInfs.isEmpty ||
             reducer(inEqConj) == InEqConj.TRUE)
      
      val reduced = reducer(toBeReduced)
      
/*      println
      println(inEqConj)
      println(toBeReduced)
      println(reduced) */
      
      {
        val allAssumptions = InEqConj.conj(Array(inEqConj, toBeReduced), to)
        assert(allAssumptions.isFalse || !allAssumptions.equalityInfs.isEmpty ||
               ReduceWithInEqs(allAssumptions, to)(reduced).isTrue)
      }

      {
        val allAssumptions = InEqConj.conj(Array(inEqConj, reduced), to)
        assert(allAssumptions.isFalse || !allAssumptions.equalityInfs.isEmpty ||
               ReduceWithInEqs(allAssumptions, to)(toBeReduced).isTrue)
      }
    }
  }

}
