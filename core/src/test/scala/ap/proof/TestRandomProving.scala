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

package ap.proof;

import ap.parameters.{Param, GoalSettings}
import ap.util.{Debug, Logic, PlainRange}
import ap.terfor.TestGenConjunctions
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.proof.goal.Goal
import ap.proof.tree.TestProofTree

import org.scalacheck.Properties
import ap.util.Prop._

class TestRandomProving extends Properties("TestRandomProving") {

  Debug.enableAllAssertions(true)

  private val tg = new TestGenConjunctions
  
  import tg.{randomEqConj, randomConj, to}
  
  // proving with only equations
  property("testEqFormulas1") = {
    testProveFormulas(6, 100,
                      randomEqConj(_, 5, 8),
                      ConstraintSimplifier.NO_SIMPLIFIER)
    true
  }

  property("testEqFormulas2") = {
    testProveFormulas(5, 60,
                      randomEqConj(_, 4, 6),
                      ConstraintSimplifier.FAIR_SIMPLIFIER)
    true
  }

  // proving with equations and inequalities
  property("testFormulas1") = {
    testProveFormulas(6, 100,
                      randomConj(_, 5, 8),
                      ConstraintSimplifier.NO_SIMPLIFIER)
    true
  }

  property("testFormulas2") = {
    testProveFormulas(5, 60,
                      randomConj(_, 4, 6),
                      ConstraintSimplifier.FAIR_SIMPLIFIER)
    true
  }

  private def testProveFormulas(maxSize : Int, iterations : Int,
                                forGen : (Int) => Conjunction,
                                simplifier : ConstraintSimplifier) = {
    val settings = Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT, simplifier)
    val prover = new ExhaustiveProver(settings)
    
    for (sizeFactor <- PlainRange(0, maxSize); _ <- PlainRange(iterations)) {
      var formula = forGen(sizeFactor)

      // ensure that the formula does not contain free variables
      while (!formula.variables.isEmpty)
        formula = Conjunction.quantify(Array(Quantifier.ALL), formula, to)
      
/*            println()
            println(formula) */

      val tree = prover(formula, to)
      val _ = tree.closingConstraint

/*      println()
    println("After many steps:")
println(tree) */

      try {
      TestProofTree.assertNormalisedTree(tree)
      } catch {
        case _ : AssertionError => prover(formula, to)
      }
    }
  }
    
}
