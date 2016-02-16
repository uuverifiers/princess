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

package ap.proof;

import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.proof.goal.{Goal, TaskManager, FactsNormalisationTask, CompoundFormulas}
import ap.proof.tree._
import ap.proof.certificates.BranchInferenceCollection
import ap.terfor._
import ap.terfor.conjunctions.{Conjunction, Quantifier, NegatedConjunctions}
import ap.terfor.substitutions.{ConstantSubst, IdentitySubst}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.basetypes.IdealInt
import ap.parameters.{GoalSettings, Param}

class TestEquationSystems(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testEqs1" => testEqs1
      case "testEqs2" => testEqs2
      case "testQuantifiedEqs1" => testQuantifiedEqs1
      case "testDivisibility1" => testDivisibility1
    }
  }

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  
  private def randomInput(len : Int) = for (i <- PlainRange(0, len))
                                       yield (IdealInt(Debug.random(-20, 20)),
                                              constsOne(Debug.random(0, constsOne.size)))

  private def randomLC(len : Int) = LinearCombination(randomInput(len), to)

  private def randomAC(eqNum : Int, maxEqSize : Int) : ArithConj = {
    val posEqNum = Debug.random(0, eqNum+1)
    randomAC(posEqNum, eqNum - posEqNum, maxEqSize)
  }

  private def randomAC(posEqNum : Int, negEqNum : Int, maxEqSize : Int) : ArithConj = {
    val inputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                    .take(posEqNum).toList
    val eqConj = EquationConj(inputConj, to)
    val negInputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                       .take(negEqNum).toList
    val negEqConj = NegEquationConj(negInputConj, to)
    
    ArithConj(eqConj, negEqConj, InEqConj.TRUE, to)
  }

  private val settings =
    Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT,
                                    ConstraintSimplifier.FAIR_SIMPLIFIER)
  private val prover = new ExhaustiveProver(settings)
  
  def testEqs1 = {
    for (eqNum <- PlainRange(0, 15); eqSize <- PlainRange(0, 15)) {
      val ac = randomAC(eqNum, eqSize)
      val facts = Conjunction.conj(Array(ac), to)
      for (elimNum <- PlainRange(0, consts.size + 1)) {
        val eliminatedConsts = Set.empty ++ consts.drop(consts.size - elimNum)
        val goal = Goal(facts, CompoundFormulas.EMPTY(Map()),
                        TaskManager.EMPTY, 0, eliminatedConsts, Vocabulary(to),
                        new IdentitySubst (to), BranchInferenceCollection.EMPTY,
                        settings)
        
//        println
//        println(goal)
    
        val tree = FactsNormalisationTask(goal,
          new SimpleProofTreeFactory(false, ConstraintSimplifier.FAIR_SIMPLIFIER))

        TestProofTree.assertNormalisedTree(tree)

//          println("After one step:")
//          println(tree)
      
          
      }
    }
  }
  
  def testEqs2 = {
    var eqs : Formula =
      EquationConj(LinearCombination(Array((IdealInt.ONE, consts(0)),
                                           (IdealInt(-5), consts(1)),
                                           (IdealInt(-1), OneTerm)), to), to)
    for (premNum <- PlainRange(1, consts.size - 1)) {
      eqs = Conjunction.conj(Array(EquationConj(LinearCombination(
                                     Array((IdealInt(4), consts(premNum)),
                                           (IdealInt(-5), consts(premNum+1)),
                                           (IdealInt(-1), OneTerm)), to), to),
                                   eqs), to)
      
//        println(goal)
//        println(goal.closingConstraint)
    
        val tree = prover(Conjunction.negate(eqs, to), to)
//          println("After many steps:")
//          println(tree)
//          println(tree.closingConstraint)
      
          TestProofTree.assertNormalisedTree(tree)
    }
  }
  
  def testDivisibility1 = {
    val div1 = Conjunction.quantify(Array(Quantifier.EX),
      EquationConj(LinearCombination(Array((IdealInt(5), VariableTerm(0)),
                                           (IdealInt(1), consts.last),
                                           (IdealInt(1), OneTerm)), to), to), to)
    val div2 = Conjunction.quantify(Array(Quantifier.EX),
      EquationConj(LinearCombination(Array((IdealInt(5), VariableTerm(0)),
                                           (IdealInt(1), consts.last),
                                           (IdealInt(2), OneTerm)), to), to), to)
    val f = Conjunction.disj(Array(div1, div2), to)

    for (elimConsts 
         <- List(Set.empty, Set(consts.last)).asInstanceOf[List[Set[ConstantTerm]]]) {
      val closedFor = Conjunction.quantify(Quantifier.ALL, to sort elimConsts, f, to)
      
      val tree = prover(closedFor, to)
//      println("After many steps:")
//      println(tree)
      
      TestProofTree.assertNormalisedTree(tree)
    }
  }
  
  def testQuantifiedEqs1 = {
    val settings =
      Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT,
                                      ConstraintSimplifier.NO_SIMPLIFIER)
    val prover = new ExhaustiveProver(settings)

    var num : Int = 0
    
    for (eqNum <- PlainRange(0, 15); eqSize <- PlainRange(0, 15)) {
      val ac = randomAC(eqNum, eqSize)

      for (quantNum <- List(0, 1, 2, 5, 10)) {
        var formula : Formula = ac
        for ((c, q) <- (Debug.randoms(0, consts.size) zip Debug.randoms(0, 2))
                       .take(quantNum)) {
          val const = consts(c)
          val quan = if (q == 0) Quantifier.ALL else Quantifier.EX
          val subst = ConstantSubst(const, VariableTerm(0), to)
          formula = Conjunction.quantify(Array(quan), subst(formula), to)
        }
        
/*        println
        println(num)
        num = num + 1
        println(formula) */
        

//        println(goal)
    
          val tree = prover(formula, to)
//          println("After many steps:")
//          println(tree)
      
          TestProofTree.assertNormalisedTree(tree)
      }
    }
  }

}
