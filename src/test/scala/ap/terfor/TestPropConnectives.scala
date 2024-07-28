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

package ap.terfor;

import ap.util.{Debug, Logic, PlainRange, FilterIt}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithEqs}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.{ArithConj, ReduceWithAC}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier,
                               ReduceWithConjunction}

import org.scalacheck.Properties
import ap.util.Prop._

class TestPropConnectives extends Properties("TestPropConnectives") {

  Debug.enableAllAssertions(true)
  
  private val tg = new TestGenConjunctions
  
  import tg.{randomLC, randomEqAC, randomAC, randomEqConj, randomConj, to, toRev}

  
  private def internallyPropagate(ac : ArithConj) : ArithConj = 
    ReduceWithAC(ArithConj.TRUE, to)(ac)
  
  
  /**
   * Generate arbitrary instances of <code>ArithConj</code>
   */
  property("testArithConj1") = {
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

    true
  }

  /**
   * Generate arbitrary instances of <code>ArithConj</code>
   */
  property("testArithConj2") = {
    for (eqNumConj <- PlainRange(5); eqNumDisj <- PlainRange(5); _ <- PlainRange(10)) {
      val ac = randomEqAC(eqNumConj, eqNumDisj, 8)

      ac.sortBy(toRev)
      internallyPropagate(ac)
    }

    true
  }

  property("testArithConj3") = {
    for (eqNumConj <- PlainRange(5); eqNumDisj <- PlainRange(5); inEqNum <- PlainRange(5);
         _ <- PlainRange(10)) {
      val ac = randomAC(eqNumConj, eqNumDisj, inEqNum, 8)

      ac.sortBy(toRev)
      internallyPropagate(ac)
    }

    true
  }

  property("testConj1") = {
    testConj1((sizeFactor: Int) => randomEqConj(sizeFactor, 5, 8))
    true
  }

  property("testConj2") = {
    testConj1((sizeFactor: Int) => randomConj(sizeFactor, 8, 8))
    true
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
      assertEquals(Conjunction.disjFor(Array(conj, NegatedConjunctions.FALSE), to), conj)
      assertEquals(Conjunction.disjFor(Array(conj, ArithConj.FALSE), to), conj)
      assertEquals(Conjunction.disjFor(Array(conj, EquationConj.FALSE), to), conj)
      
      // test idempotence
      assertEquals(Conjunction.conj(Array(conj, conj), to), conj)
      assertEquals(Conjunction.disj(Array(conj, conj), to), conj)
    }
  }
   
  /**
   * Generate arbitrary instances of <code>Conjunction</code> and apply
   * <code>ReduceWithAC</code> to them
   */
  property("testReduceWithConjunction1") = {
    for (sizeFactor <- PlainRange(0, 10); _ <- PlainRange(100)) {
      val toBeReduced = randomEqConj(sizeFactor, 5, 8)
      ReduceWithConjunction(Conjunction.TRUE, to)(toBeReduced)
    }
    true
  }

  property("testReduceWithConjunction2") = {
    for (sizeFactor <- PlainRange(0, 10); _ <- PlainRange(100)) {
      val toBeReduced = randomConj(sizeFactor, 5, 8)
      ReduceWithConjunction(Conjunction.TRUE, to)(toBeReduced)
    }
    true
  }
}
