/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.PresburgerTools
import ap.parameters.Param
import ap.proof.Vocabulary
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.equations.NegEquationConj
import ap.terfor.inequalities.InEqConj
import ap.types.UninterpretedSortTheory.DomainPredicate
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.util.{Debug, Seqs}

object ExQuantifierTask {

  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    f.quans.lastOption == Some(Quantifier.EX) && !f.isDivisibility

}

class ExQuantifierTask(_formula : Conjunction, _age : Int)
      extends QuantifierTask(_formula, _age) {

  // add the size of the formula to make behaviour more deterministic
  val priority : Int = 2 + age + formula.opCount

  protected val constantNameBase : String = "ex_"
    
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val (instantiatedConj, constants, newO, newBindingContext) =
      instantiateWithConstants(goal)

    val newVocabulary =
      Vocabulary(newO, newBindingContext, goal.constantFreedom)

    val singleInstantiation =
      formula.predicates subsetOf
        Param.SINGLE_INSTANTIATION_PREDICATES(goal.settings)

    val subtree = {
      implicit val no = newO
      val ineqs = instantiatedConj.arithConj.inEqs

      // extract inequality bounds on the quantified variables, which are
      // handled/ using constraints in the proof tree
      val (varBounds, remainingConj) =
        if (Seqs.disjointSeq(ineqs.constants, constants) ||
            !Param.STRENGTHEN_TREE_FOR_SIDE_CONDITIONS(goal.settings)) {
          (InEqConj.TRUE, instantiatedConj)
        } else {
          val constantSet =
            constants.toSet
          val (lc1, lc2) =
            ineqs partition { lc => lc.constants.size == 1 &&
                                    (lc.constants subsetOf constantSet) }
          (ineqs updateGeqZeroSubset lc1,
           instantiatedConj.updateInEqs(ineqs updateGeqZeroSubset lc2))
        }

      // extract domain bounds on the quantified variables, which are also
      // handled using constraints in the proof tree
      val predConj = remainingConj.predConj
      val domGuards =
        for (a <- predConj.positiveLits;
             if DomainPredicate.unapply(a.pred).isDefined)
        yield a

      val (domConstraints, remainingConj2) =
        if (domGuards.isEmpty) {
          (List(), remainingConj)
        } else {
          val otherLits =
            predConj.positiveLits filterNot (domGuards contains _)
          val newPredConj =
            predConj.updateLitsSubset(otherLits, predConj.negativeLits, newO)
          val newInst =
            remainingConj updatePredConj newPredConj
          val factPreds =
            goal.facts.predConj
          val eqGuards =
            for (g <- domGuards) yield {
              Conjunction.negate(
                NegEquationConj(for (a <- factPreds positiveLitsWithPred g.pred)
                                yield g.unify(a, newO)(0), newO), newO)
            }
          (eqGuards, newInst)
        }

      val instantiatedConjTasks =
        Goal.formulaTasks(remainingConj2, goal.age,
                          Set.empty, newVocabulary, goal.settings) ++
        Goal.formulaTasks(Conjunction.negate(varBounds, newO), goal.age,
                          Set.empty, newVocabulary, goal.settings) ++
        (for (a <- domGuards;
              t <- Goal.formulaTasks(Conjunction.negate(a, newO), goal.age,
                                     Set.empty, newVocabulary, goal.settings))
         yield t) ++
        (if (singleInstantiation) List() else goal.formulaTasks(formula))

      val newGoal =
        ptf.updateGoal(Set.empty.asInstanceOf[Set[ConstantTerm]],
                       newVocabulary, instantiatedConjTasks, goal)

      val treeConstraints =
        Conjunction.conj(domConstraints ++ List(varBounds), newO)

      if (treeConstraints.isTrue)
        newGoal
      else
        ptf.strengthen(newGoal, treeConstraints, newVocabulary)
    }

    ptf.quantify(subtree, Quantifier.EX, constants, goal.vocabulary, newO)
  }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new ExQuantifierTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    ExQuantifierTask.isCoveredFormula(f)

}
