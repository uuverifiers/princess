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

package ap.terfor;

import ap.util.{Debug, Logic, APTestCase, PlainRange, FilterIt}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithEqs}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.{ArithConj, ReduceWithAC}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier,
                               ReduceWithConjunction}

class TestPropConnectives(n : String) extends APTestCase(n) {

  
  private val tg = new TestGenConjunctions
  
  import tg.{randomLC, randomEqAC, randomAC, randomEqConj, randomConj, to, toRev}

  
  def runTest = {
    n match {
      case "testArithConj1" => testArithConj1
      case "testArithConj2" => testArithConj2
      case "testArithConj3" => testArithConj3
      case "testConj1" => testConj1((sizeFactor: Int) => randomEqConj(sizeFactor, 5, 8))
      case "testConj2" => testConj1((sizeFactor: Int) => randomConj(sizeFactor, 8, 8))
      case "testReduceWithConjunction1" => testReduceWithConjunction1
      case "testReduceWithConjunction2" => testReduceWithConjunction2
    }
  }


  
  private def internallyPropagate(ac : ArithConj) : ArithConj = 
    ReduceWithAC(ArithConj.TRUE, to)(ac)
  
  
  /**
   * Generate arbitrary instances of <code>ArithConj</code>
   */
  def testArithConj1 = {
    for (eqNumConj <- PlainRange(5); eqNumDisj <- PlainRange(5); _ <- PlainRange(10)) {
      val inputConj = (for (len <- Debug.randoms(0, 8)) yield randomLC(len))
                      .take(eqNumConj).toList
      val eqConj = EquationConj(inputConj, to)
      val negInputConj = (for (len <- Debug.randoms(0, 8)) yield randomLC(len))
                         .take(eqNumDisj).toList
      val negEqConj = NegEquationConj(negInputConj, to)
      
      val ac = ArithConj(eqConj, negEqConj, InEqConj.TRUE, to)
      val ac2 = ArithConj.conj((for (lc <- inputConj) yield EquationConj(lc, to)) :::
                               (for (lc <- negInputConj) yield NegEquationConj(lc, to)),
                               to)

      assertEquals(ac, ac2)
                               
      ac.sortBy(toRev)
      internallyPropagate(ac)
    }
  }

  /**
   * Generate arbitrary instances of <code>ArithConj</code>
   */
  def testArithConj2 = {
    for (eqNumConj <- PlainRange(5); eqNumDisj <- PlainRange(5); _ <- PlainRange(10)) {
      val ac = randomEqAC(eqNumConj, eqNumDisj, 8)

      ac.sortBy(toRev)
      internallyPropagate(ac)
    }
  }

  def testArithConj3 = {
    for (eqNumConj <- PlainRange(5); eqNumDisj <- PlainRange(5); inEqNum <- PlainRange(5);
         _ <- PlainRange(10)) {
      val ac = randomAC(eqNumConj, eqNumDisj, inEqNum, 8)

      ac.sortBy(toRev)
      internallyPropagate(ac)
    }
  }

  /**
   * Generate arbitrary instances of <code>Conjunction</code> and perform
   * various operations on them
   */
  def testConj1(conjGen : (Int) => Conjunction) = {
    for (sizeFactor <- PlainRange(0, 10); _ <- PlainRange(100)) {
      val conj = conjGen(sizeFactor)
      conj.constants
      conj.variables
      
//      println(conj)
      
      // test what happens when the free variables are quantified
      var quantConj = conj
//      println("Quantifying ...")
      while (!quantConj.variables.isEmpty) {
        val newQuantConj =
          Conjunction.quantify(Array(Quantifier.ALL), quantConj, to)
//          println(newQuantConj)
        assertEquals(newQuantConj.constants, conj.constants)
        assertEquals(newQuantConj.variables,
                     for (VariableTerm(i) <- quantConj.variables; if (i >= 1))
                     yield VariableTerm(i - 1))
	quantConj = newQuantConj
      }

      // test to change the ordering of a conjunction
      val conjRev = conj.sortBy(toRev)
      conjRev.constants
      conjRev.variables
      
      // test negation
      assertEquals(conj.negate.negate, conj)
      
      // test conjunction/disjunction with neutral elements
      assertEquals(Conjunction.conj(Array(conj, Conjunction.TRUE), to), conj)
      assertEquals(Conjunction.conj(Array(conj, NegatedConjunctions.TRUE), to), conj)
      assertEquals(Conjunction.conj(Array(conj, ArithConj.TRUE), to), conj)
      assertEquals(Conjunction.conj(Array(conj, EquationConj.TRUE), to), conj)
      assertEquals(Conjunction.disj(Array(conj, Conjunction.FALSE), to), conj)
      assertEquals(Conjunction.disj(Array(conj, NegatedConjunctions.FALSE), to), conj)
      assertEquals(Conjunction.disj(Array(conj, ArithConj.FALSE), to), conj)
      assertEquals(Conjunction.disj(Array(conj, EquationConj.FALSE), to), conj)
      
      // test idempotence
      assertEquals(Conjunction.conj(Array(conj, conj), to), conj)
      assertEquals(Conjunction.disj(Array(conj, conj), to), conj)
    }
  }
   
  /**
   * Generate arbitrary instances of <code>Conjunction</code> and apply
   * <code>ReduceWithAC</code> to them
   */
  def testReduceWithConjunction1 = {
     for (sizeFactor <- PlainRange(0, 10); _ <- PlainRange(100)) {
       val toBeReduced = randomEqConj(sizeFactor, 5, 8)
       ReduceWithConjunction(Conjunction.TRUE, to)(toBeReduced)
     }
  }

  def testReduceWithConjunction2 = {
    for (sizeFactor <- PlainRange(0, 10); _ <- PlainRange(100)) {
      val toBeReduced = randomConj(sizeFactor, 5, 8)
      ReduceWithConjunction(Conjunction.TRUE, to)(toBeReduced)
    }
  }
}
