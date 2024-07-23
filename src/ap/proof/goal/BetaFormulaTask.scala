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

package ap.proof.goal;

import ap.proof._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{Formula, ConstantTerm, TerFor}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.VariableSubst
import ap.terfor.preds.PredConj
import ap.util.{Debug, PlainRange, Seqs, FilterIt}
import ap.parameters.{Param, GoalSettings}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.{BranchInferenceCollection, Certificate,
                              BetaCertificate, PartialCertificate, CertFormula}

import scala.collection.immutable.VectorBuilder

object BetaFormulaTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
  def apply(formula : Conjunction,
            age : Int,
            eliminatedConstants : Set[ConstantTerm],
            vocabulary : Vocabulary,
            settings : GoalSettings) =
    new BetaFormulaTask(formula,
                        !splittingNecessary(formula,
                                            eliminatedConstants,
                                            vocabulary,
                                            settings),
                        age,
                        Param.SYMBOL_WEIGHTS(settings))
  
  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    f.size > 1 && f.quans.isEmpty

  /**
   * Split a conjunction <code>selectedConjunct & otherConjuncts</code> in
   * the antecedent
   */
  protected[goal] def doSplit(selectedConjunct : Conjunction,
                              otherConjuncts : Conjunction,
                              remainingCompoundFormulas : CompoundFormulas,
                              goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val negSelectedConjunct = selectedConjunct.negate

    val firstTree = {
      // assume that the cut-literal is true
      val remTasks = goal.formulaTasks(otherConjuncts)
      val introLemma = introduceLemma(selectedConjunct, otherConjuncts, goal)
      
      val allTasks = if (introLemma)
                       // make a real cut
                       remTasks ++ goal.formulaTasks(negSelectedConjunct)
                     else
                       remTasks

      ptf.updateGoal(remainingCompoundFormulas, allTasks,
                     goal startNewInferenceCollection (
                       List(otherConjuncts.negate) :::
                       (if (introLemma) List(selectedConjunct) else List())),
                     goal)
    }
    
    val secondTree = {
      // assume that the cut-literal is false
      ptf.updateGoal(remainingCompoundFormulas,
                     goal formulaTasks selectedConjunct,
                     goal startNewInferenceCollection List(negSelectedConjunct),
                     goal)
    }
    
    if (Param.PROOF_CONSTRUCTION(goal.settings)) {
      val order = goal.order
      val branchInferences = goal.branchInferences
    
      val leftFormula = CertFormula(selectedConjunct.negate)
      val rightFormula = CertFormula(otherConjuncts.negate)
      
      def pCertFunction(children : Seq[Certificate]) : Certificate =
        BetaCertificate(leftFormula, rightFormula, true,
                        children(0), children(1), order)
      
      ptf.and(Array(secondTree, firstTree),
              PartialCertificate(pCertFunction _,
                                 BetaCertificate.providedFormulas(
                                     leftFormula, rightFormula, true),
                                 branchInferences, order),
              goal.vocabulary)
    } else {
      ptf.and(Array(secondTree, firstTree), goal.vocabulary)
    }
  }
  
  private def introduceLemma(cutLiteral : Conjunction,
                             otherConjuncts : Conjunction,
                             goal : Goal) : Boolean =
    cutLiteral.isLiteral && {
      if (cutLiteral.predConj.isTrue)
        // the cut-literal is an arithmetic literal
        !otherConjuncts.predicates.isEmpty ||
        cutLiteral.arithConj.negativeEqs.isEmpty ||
        (cutLiteral.constants subsetOf goal.eliminatedConstants)
      else
        // the cut-literal is a predicate literal
        cutLiteral.constants subsetOf goal.eliminatedConstants
    }
  
  /**
   * Determine whether this formula requires real splitting, or whether it can
   * be passed to the constraint unchanged
   */
  private def splittingNecessary(formula : Conjunction,
                                 eliminatedConstants : Set[ConstantTerm],
                                 vocabulary : Vocabulary,
                                 settings : GoalSettings) : Boolean =
    Param.PROOF_CONSTRUCTION(settings) ||
    !formula.predicates.isEmpty ||
    !vocabulary.constantFreedom.isShielded(formula, vocabulary.bindingContext) &&
    (Param.FULL_SPLITTING(settings) ||
     !Conjunction.collectQuantifiers(formula).isEmpty ||
     !Seqs.disjoint(eliminatedConstants, formula.constants))

}


class BetaFormulaTask(_formula : Conjunction, val addToQFClauses : Boolean,
                      _age : Int, symbolWeights : SymbolWeights)
      extends FormulaTask(_formula, _age) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(BetaFormulaTask.AC,
                   !formula.isTrue && !formula.isFalse &&
                   !formula.isLiteral && !formula.isNegatedConjunction)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
      
  val priority : Int =
    (if (addToQFClauses)
       -10000
     else
       -400 - (symbolWeights maxWeight formula) / 100 +
       (symbolWeights minAbbrevWeight formula).getOrElse(0) * 10 +
       formula.arithConj.size * 5 +
       formula.predConj.size * 1 +
       formula.negatedConjs.size * 5) + age

  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    if (addToQFClauses) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(BetaFormulaTask.AC,
                      !BetaFormulaTask.splittingNecessary(formula,
                                                          goal.eliminatedConstants,
                                                          goal.vocabulary,
                                                          goal.settings))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      ptf.updateGoalAddQFClause(formula, goal)
    } else {
      if (formula.arithConj.isTrue && formula.predConj.isTrue) {
        // split to handle the complex conjuncts
        splitNegatedConjs(goal, ptf)
      } else {
        // cut over one of the literals
        applyCut(goal, ptf)
      }
    }

     
  private def splitNegatedConjs(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaFormulaTask.AC, formula.negatedConjs.size > 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val subtrees = for (negConj <- formula.negatedConjs)
                   yield ptf.updateGoal(goal.formulaTasks(negConj.negate),
                                        goal startNewInferenceCollection List(negConj),
                                        goal)

    if (Param.PROOF_CONSTRUCTION(goal.settings)) {
      val order = goal.order
      val branchInferences = goal.branchInferences
      val negatedConjs = formula.negatedConjs
    
      def pCertFunction(children : Seq[Certificate]) : Certificate =
        BetaCertificate((for ((f, c) <- negatedConjs.iterator zip children.iterator)
                           yield (CertFormula(f), c)).toList,
                        order)
      
      ptf.and(subtrees,
              PartialCertificate(pCertFunction _,
                                 for (f <- negatedConjs) yield Set(CertFormula(f)),
                                 branchInferences, order),
              goal.vocabulary)
    } else {
      ptf.and(subtrees, goal.vocabulary)
    }
  }

  private def applyCut(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val (cutLiteral, rem) = selectCutLiteral(formula, goal)
    BetaFormulaTask.doSplit(cutLiteral, rem, goal.compoundFormulas, goal, ptf)
  }
  
  //////////////////////////////////////////////////////////////////////////////
      
  /**
   * Given a conjunction of formulas, select one of the formulas
   * as literal to cut over. The result is the pair of the selected formula and
   * the remaining <code>Conjunction</code>
   */
  private def selectCutLiteral(conj : Conjunction, goal : Goal)
                                              : (Conjunction, Conjunction) = {
    val weights = Param.SYMBOL_WEIGHTS(goal.settings)
    if (conj.predConj.isTrue) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(BetaFormulaTask.AC, !conj.arithConj.isTrue)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val (sel, rem) =
        selectCutLiteral(conj.arithConj, goal.eliminatedConstants, weights)
      (Conjunction.conj(sel, conj.order), conj.updateArithConj(rem)(conj.order))      
    } else {
      val (sel, rem) =
        selectHeaviestLiteral(conj.predConj, (p) => weights maxWeight p)
      (Conjunction.conj(sel, goal.order), conj.updatePredConj(rem)(conj.order))
    }
  }

  //////////////////////////////////////////////////////////////////////////////
   
  private def selectHeaviestLiteral(conj : PredConj,
                                    weighter : (PredConj) => Int)
                                 : (PredConj, PredConj) = {
    val (bestLit, remainingLits) =
      selectHeaviestLiteral(conj.iterator, weighter)
    (bestLit, PredConj.conj(remainingLits, conj.order))
  }

  private def selectHeaviestLiteral[A <: TerFor]
                                   (lits : Iterator[A], weighter : (A) => Int)
                                 : (A, IndexedSeq[A]) = {
    val remainingLits = new VectorBuilder[A]
    var bestLit : A = lits.next()  // lits has to be non-empty
    var bestVal : Int = weighter(bestLit)
    
    for (c <- lits) {
      val newVal = weighter(c)
      if (newVal > bestVal) {
        remainingLits += bestLit
        bestLit = c
        bestVal = newVal
      } else {
        remainingLits += c
      }
    }
    
    (bestLit, remainingLits.result())
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def selectCutLiteralXX(ac : ArithConj,
                               eliminatedConstants : Set[ConstantTerm],
                               weights : SymbolWeights)
                                                : (ArithConj, ArithConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaFormulaTask.AC, !ac.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (bestLit, remainingLits) =
      selectHeaviestLiteral(ac.iterator, (p:ArithConj) => weights maxWeight p)
    (bestLit, ArithConj.conj(remainingLits, ac.order))    
  }

  private def selectCutLiteral(ac : ArithConj,
                               eliminatedConstants : Set[ConstantTerm],
                               weights : SymbolWeights)
                                         : (ArithConj, ArithConj) = {
    def selectPositiveEq = {
      val (sel, rem) = selectCutLiteral(ac.positiveEqs, weights)
      (ArithConj.conj(sel, ac.order), ac.updatePositiveEqs(rem)(ac.order))      
    }
    def selectNegativeEq = {
      val (sel, rem) = selectCutLiteral(ac.negativeEqs, weights)
      (ArithConj.conj(sel, ac.order), ac.updateNegativeEqs(rem)(ac.order))      
    }
    def selectInEq = {
      val (sel, rem) = selectCutLiteral(ac.inEqs, weights)
      (ArithConj.conj(sel, ac.order), ac.updateInEqs(rem)(ac.order))      
    }
    
    // try to select a cut-literal that contains eliminated constants
    (ac.positiveEqs.isEmpty,
       Seqs.disjoint(eliminatedConstants, ac.positiveEqs.constants),
     ac.negativeEqs.isEmpty,
       Seqs.disjoint(eliminatedConstants, ac.negativeEqs.constants),
     ac.inEqs.isEmpty,
       Seqs.disjoint(eliminatedConstants, ac.inEqs.constants)) match {
      
      case (false, false, _, _, _, _) => selectPositiveEq
      case (_, _, _, _, false, false) => selectInEq
      case (_, _, false, false, _, _) => selectNegativeEq
      case (false, _, _, _, _, _)     => selectPositiveEq
      case (_, _, _, _, false, _)     => selectInEq
      case (_, _, false, _, _, _)     => selectNegativeEq
      
      case _ => { assert(false); null }

    }
  }

  private def selectCutLiteral(eqs : EquationConj, weights : SymbolWeights)
                                           : (EquationConj, EquationConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaFormulaTask.AC, !eqs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (bestLit, remainingLits) =
      selectHeaviestLiteral(eqs.iterator, lcWeighter(weights))
    (EquationConj(bestLit, eqs.order), eqs.updateEqs(remainingLits)(eqs.order))
  }

  private def selectCutLiteral(eqs : NegEquationConj, weights : SymbolWeights)
                                      : (NegEquationConj, NegEquationConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaFormulaTask.AC, !eqs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (bestLit, remainingLits) =
      selectHeaviestLiteral(eqs.iterator, lcWeighter(weights))
    (NegEquationConj(bestLit, eqs.order),
     eqs.updateEqs(remainingLits)(eqs.order))
  }
  
  private def selectCutLiteral(inEqs : InEqConj, weights : SymbolWeights)
                                                   : (InEqConj, InEqConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaFormulaTask.AC, !inEqs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (bestLit, remainingLits) =
      selectHeaviestLiteral(inEqs.iterator, lcWeighter(weights))
    (InEqConj(bestLit, inEqs.order), InEqConj(remainingLits, inEqs.order))
  }

  //////////////////////////////////////////////////////////////////////////////

  private def size(eqs : Iterable[LinearCombination]) : Int =
    (0 /: (for (lc <- eqs.iterator) yield lc.size)) ((s:Int, n:Int) => s+n)

  private def size(ac : ArithConj) : Int =
    size(ac.positiveEqs) + size(ac.negativeEqs) + size(ac.inEqs)
    
  private def lcWeighter(weights : SymbolWeights) =
    (lc : LinearCombination) => (weights maxWeight lc) - lc.size * 100
    
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Update the task with possibly new information from the goal
   */
  override def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                         : Seq[FormulaTask] =
    if (addToQFClauses &&
        BetaFormulaTask.splittingNecessary(formula, goal.eliminatedConstants,
                                           goal.vocabulary, goal.settings))
      // we have to make sure that the flag <code>addToQFClauses</code> is reset
      this.updateFormula(formula, goal).updateTask(goal, factCollector)
    else
      super.updateTask(goal, factCollector)

  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    BetaFormulaTask(f, age, goal.eliminatedConstants, goal.vocabulary, goal.settings)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    BetaFormulaTask.isCoveredFormula(f)

  val name : String = "BetaFor"

}
