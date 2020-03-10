/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

  val priority : Int = 5 + age

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
