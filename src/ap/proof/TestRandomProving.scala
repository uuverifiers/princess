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

package ap.proof;

import ap.parameters.{Param, GoalSettings}
import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.terfor.TestGenConjunctions
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.proof.goal.Goal
import ap.proof.tree.TestProofTree

class TestRandomProving(n : String) extends APTestCase(n) {

  private val tg = new TestGenConjunctions
  
  import tg.{randomEqConj, randomConj, to}
  
  def runTest = {
    n match {
      // proving with only equations
      case "testEqFormulas1" => testProveFormulas(6, 100,
                                                  randomEqConj(_, 5, 8),
                                                  ConstraintSimplifier.NO_SIMPLIFIER)
      case "testEqFormulas2" => testProveFormulas(5, 60,
                                                  randomEqConj(_, 4, 6),
                                                  ConstraintSimplifier.FAIR_SIMPLIFIER)
      // proving with equations and inequalities
      case "testFormulas1" =>   testProveFormulas(6, 100,
                                                  randomConj(_, 5, 8),
                                                  ConstraintSimplifier.NO_SIMPLIFIER)
      case "testFormulas2" =>   testProveFormulas(5, 60,
                                                  randomConj(_, 4, 6),
                                                  ConstraintSimplifier.FAIR_SIMPLIFIER)
    }
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
      
/*            println
            println(formula) */

        println(formula)
      val tree = prover(formula, to)
      tree.closingConstraint

/*      println
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
