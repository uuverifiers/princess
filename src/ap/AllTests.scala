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

package ap;

import ap.util.APTestCase

import scala.collection.mutable.ArrayBuffer

object AllTests extends App {

  val tests = new ArrayBuffer[APTestCase]  

  def addTest(t : APTestCase) = (tests += t)

  def run(r : APTestCase.TestResult) : Unit =
    for (t <- tests)
      t.run(r)

  addTest(new ap.basetypes.TestIdealInt ("testDiv"))
  addTest(new ap.basetypes.TestIdealInt ("testReduceAbs"))
  addTest(new ap.basetypes.TestIdealInt ("testGcdAndCofactors1"))
  addTest(new ap.basetypes.TestIdealInt ("testGcdAndCofactorsSeq"))
  addTest(new ap.basetypes.TestIdealInt ("testGcdSeq"))
  addTest(new ap.basetypes.TestLeftistHeap ("testInsertElements"))
  addTest(new ap.basetypes.TestLeftistHeap ("testInsertIterator"))
  addTest(new ap.basetypes.TestLeftistHeap ("testInsertHeap"))
  addTest(new ap.basetypes.TestLeftistHeap ("testRemoveAll"))
  addTest(new ap.basetypes.TestLeftistHeap ("testLargeHeap"))
  addTest(new ap.basetypes.TestLeftistHeap ("testHeapCollector"))
  addTest(new ap.basetypes.TestLeftistHeap ("testFlatMap"))
  addTest(new ap.terfor.TestTermOrder ("testSimpleExtension"))
  addTest(new ap.terfor.TestTermOrder ("testConditionalExtension"))
  addTest(new ap.terfor.TestTermOrder ("testLinearCombinationComparison"))
  addTest(new ap.terfor.TestPropConnectives ("testArithConj1"))
  addTest(new ap.terfor.TestPropConnectives ("testArithConj2"))
  addTest(new ap.terfor.TestPropConnectives ("testArithConj3"))
  addTest(new ap.terfor.TestPropConnectives ("testConj1"))
  addTest(new ap.terfor.TestPropConnectives ("testConj2"))
  addTest(new ap.terfor.TestPropConnectives ("testReduceWithConjunction1"))
  addTest(new ap.terfor.TestPropConnectives ("testReduceWithConjunction2"))
  addTest(new ap.terfor.linearcombination.TestLinearCombination ("testLC1"))
  addTest(new ap.terfor.linearcombination.TestLinearCombination ("testLCFlatten"))
  addTest(new ap.terfor.linearcombination.TestLinearCombination ("testLCAddition1"))
  addTest(new ap.terfor.linearcombination.TestLinearCombination ("testLCAddition2"))
  addTest(new ap.terfor.linearcombination.TestLinearCombination ("testLCAddition3"))
  addTest(new ap.terfor.equations.TestEquationSet ("testConj1"))
  addTest(new ap.terfor.equations.TestEquationSet ("testNegConj1"))
  addTest(new ap.terfor.equations.TestEquationSet ("testReduceWithEqs1"))
  addTest(new ap.terfor.equations.TestEquationSet ("testReduceWithEqs2"))
  addTest(new ap.terfor.equations.TestEquationSet ("testReduceWithEqs3"))
  addTest(new ap.terfor.equations.TestEquationSet ("testReduceDisj"))
  addTest(new ap.terfor.inequalities.TestInequalities ("testConj1"))
  addTest(new ap.terfor.inequalities.TestInequalities ("testConj2"))
  addTest(new ap.terfor.inequalities.TestInequalities ("testReduceWithInEqs1"))
  addTest(new ap.terfor.inequalities.TestInequalities ("testReduceWithInEqs2"))
  addTest(new ap.terfor.substitutions.TestSubst ("testPseudoSubst"))  
  addTest(new ap.proof.TestEquationSystems ("testEqs1"))
  addTest(new ap.proof.TestEquationSystems ("testEqs2"))
  addTest(new ap.proof.TestEquationSystems ("testQuantifiedEqs1"))
  addTest(new ap.proof.TestEquationSystems ("testDivisibility1"))
  addTest(new ap.proof.TestRandomProving ("testEqFormulas1"))
  addTest(new ap.proof.TestRandomProving ("testEqFormulas2"))
  addTest(new ap.proof.TestRandomProving ("testFormulas1"))
  addTest(new ap.proof.TestRandomProving ("testFormulas2"))
  addTest(new ap.parser.TestInputAbsyVisitor ("testDepthVisitor"))
  addTest(new ap.parser.TestInputAbsyVisitor ("testSubstVisitor"))
  addTest(new ap.parser.TestInputAbsyVisitor ("testInputAbsy2Internal"))

  val timeBefore = System.currentTimeMillis
  
  val r = new APTestCase.TestResult()
  run(r)
  
  val timeAfter = System.currentTimeMillis
    
  println
  println("Time needed: " + (timeAfter - timeBefore) + "ms")
  println
  
  for(tf <- r.exceptions) { 
    tf.printStackTrace
  }
  
}
