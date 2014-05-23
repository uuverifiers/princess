/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal;

import ap.PresburgerTools
import ap.proof.Vocabulary
import ap.terfor.{ConstantTerm, TerForConvenience}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.util.Debug
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.parameters.Param
import ap.terfor.equations.NegEquationConj

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
    val (rawInstantiatedConj, constants, newOrder, newBindingContext) =
      instantiateWithConstants(goal)

    ////////////////////////////////////////////////////////////////////////////

    val finDomConstraints = Param.FINITE_DOMAIN_CONSTRAINTS(goal.settings)

    val (instantiatedConj, guard) = finDomConstraints match {
      case Param.FiniteDomainConstraints.TypeGuards => {

        implicit val _ = newOrder
  
        // are there any type guards to be satisfied?
        val domainPredicates = Param.DOMAIN_PREDICATES(goal.settings)
        
        val predConj = rawInstantiatedConj.predConj
        val (guards, otherLits) =
          predConj.positiveLits partition { a => domainPredicates contains a.pred }
        
        if (guards.isEmpty) {
          (rawInstantiatedConj, Conjunction.TRUE)
        } else {
          val newInst =
            Conjunction.conj(guards, newOrder) ==>
            rawInstantiatedConj.updatePredConj(
              predConj.updateLits(otherLits, predConj.negativeLits))
          val eqGuard =
            !Conjunction.disjFor(
               for (g <- guards.iterator)
               yield {
                 //-BEGIN-ASSERTION-//////////////////////////////////////////////
                 Debug.assertInt(ExQuantifierTask.AC, g.pred.arity == 1)
                 //-END-ASSERTION-////////////////////////////////////////////////
                 NegEquationConj(for (a <- goal.facts.predConj positiveLitsWithPred g.pred)
                                 yield g.unify(a, newOrder)(0), newOrder)
               }, newOrder)
          (newInst, eqGuard)
        }

      }

      case Param.FiniteDomainConstraints.VocabularyEquations => {
        import TerForConvenience._
        implicit val _ = newOrder

        val guard =
          conj(for (c <- constants.iterator)
               yield disjFor(for (d <- goal.bindingContext.universallyBoundConstants)
                             yield (c === d)))
        (rawInstantiatedConj, guard)
      }

      case Param.FiniteDomainConstraints.DomainSize => {
        import TerForConvenience._
        implicit val _ = newOrder

        val guard =
          conj(for (c <- constants.iterator)
               yield (c >= 0 & c < ap.CmdlMain.domain_size))
        (rawInstantiatedConj, guard)
      }

      case Param.FiniteDomainConstraints.None =>
        (rawInstantiatedConj, Conjunction.TRUE)
    }

    ////////////////////////////////////////////////////////////////////////////

    val newVocabulary =
      Vocabulary(newOrder, newBindingContext, goal.constantFreedom)

    val subtree =
      if (!formula.predicates.isEmpty) {
        // can some of the Presburger conditions be extracted and added as
        // constraints to the proof tree?

/*        val (withoutPredsIt, withPredsIt) =
          instantiatedConj.iterator partition (_.predicates.isEmpty)
        val withPredsList = withPredsIt.toList
        val withoutPreds = Conjunction.conj(withoutPredsIt, newOrder)

        if (!withoutPreds.isTrue &&
            withPredsList.size == 1 &&
            PresburgerTools.isValid(
              Conjunction.quantify(Quantifier.EX, constants, withoutPreds, newOrder))) {
          val withPreds = Conjunction.conj(withPredsList, newOrder)
        
          val instantiatedConjTask =
            Goal.formulaTasks(withPreds, goal.age,
                              Set.empty, newVocabulary, goal.settings) ++
            Goal.formulaTasks(withoutPreds.negate, goal.age,
                              Set.empty, newVocabulary, goal.settings)

          ptf.strengthen(
            ptf.updateGoal(Set.empty.asInstanceOf[Set[ConstantTerm]],
                           newVocabulary,
                           instantiatedConjTask ++ goal.formulaTasks(formula),
                           goal),
            withoutPreds, newVocabulary)
        } else { */
          val instantiatedConjTask =
            Goal.formulaTasks(instantiatedConj, goal.age,
                              Set.empty, newVocabulary, goal.settings)
          ptf.updateGoal(Set.empty.asInstanceOf[Set[ConstantTerm]],
                         newVocabulary,
                         instantiatedConjTask ++ goal.formulaTasks(formula),
                         goal)
//        }

      } else {

        val instantiatedConjTask =
            Goal.formulaTasks(instantiatedConj, goal.age,
                             Set.empty, newVocabulary, goal.settings)
        ptf.updateGoal(Set.empty.asInstanceOf[Set[ConstantTerm]],
                       newVocabulary,
                       instantiatedConjTask,
                       goal)

    }

    ptf.quantify(
      if (guard.isTrue)
        subtree
      else
        ptf.strengthen(subtree, guard, newVocabulary),
      Quantifier.EX, constants, goal.vocabulary, newOrder)
  }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new ExQuantifierTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    ExQuantifierTask.isCoveredFormula(f)

}
