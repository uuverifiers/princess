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
        
//        println()
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
        
/*        println()
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
