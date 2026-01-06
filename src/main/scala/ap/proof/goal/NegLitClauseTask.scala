/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2025 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions,
                               Quantifier, IterativeClauseMatcher}
import ap.terfor.preds.PredConj
import ap.parameters.{Param, GoalSettings}
import ap.Signature.PredicateMatchConfig
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.BranchInferenceCollector
import ap.util.{Debug, Logic, Seqs}

object NegLitClauseTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction, config : PredicateMatchConfig) : Boolean =
    (!f.quans.isEmpty &&
     (f.quans forall (Quantifier.EX ==)) &&
     ((IterativeClauseMatcher.predConjIsMatchable(f, config)) !=
         IterativeClauseMatcher.Matchable.No)
    // TODO: find a proper condition when nested quantifiers can be allowed here
    // f.negatedConjs.isEmpty
     ) || (
     f.isNegatedConjunction &&
     (f negatedConjs 0).isPurelyNegated &&
     ((f negatedConjs 0).negatedConjs forall (isCoveredFormula(_, config))))

   def isCoveredFormula(f : Conjunction, settings : GoalSettings) : Boolean =
     isCoveredFormula(f,
                      Param.PREDICATE_MATCH_CONFIG(settings))

   def apply(_formula : Conjunction, _age : Int,
             settings : GoalSettings) =
     new NegLitClauseTask(_formula, _age,
                          Param.PREDICATE_MATCH_CONFIG(settings))
}

class NegLitClauseTask(_formula : Conjunction, _age : Int,
                       predicateMatchConfig : PredicateMatchConfig)
                       extends FormulaTask(_formula, _age) {

  val priority : Int = -10000 + age

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(NegLitClauseTask.AC, !formula.isTrue)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val (eagerClauses, lazyClauses) =
      if (formula.isNegatedConjunction)
        (formula negatedConjs 0).negatedConjs partition (isEagerClause(_))
      else
        isMatchable(formula) match {
          case IterativeClauseMatcher.Matchable.Complete     => (Seq(formula), Seq())
          case IterativeClauseMatcher.Matchable.ProducesLits => (Seq(), Seq(formula))
        }

    val collector = goal.getInferenceCollector

    val oldCF = goal.compoundFormulas
    val (newCF1, tasks1) = updateMatcher(oldCF, goal, collector, true, eagerClauses)
    val (newCF2, tasks2) = updateMatcher(newCF1, goal, collector, false, lazyClauses)
    
    ptf.updateGoal(newCF2, tasks1 ++ tasks2, collector.getCollection, goal)
  }
  
  private def isEagerClause(f : Conjunction) =
    isMatchable(f) == IterativeClauseMatcher.Matchable.Complete

  private def isMatchable(f : Conjunction) =
    IterativeClauseMatcher.predConjIsMatchable(f, predicateMatchConfig)
    
  private def updateMatcher(cf : CompoundFormulas,
                            goal : Goal,
                            collector : BranchInferenceCollector,
                            eager : Boolean,
                            addedClauses : Iterable[Conjunction])
                           : (CompoundFormulas, Iterable[FormulaTask]) =
    if (addedClauses.isEmpty) {
      (cf, List())
    } else {
      val order = goal.order
      val voc = goal.vocabulary
    
      val oldMatcher = cf.quantifierClauses(eager)
    
      val reverseProp = Param.REVERSE_FUNCTIONALITY_PROPAGATION(goal.settings)
      val (instances, newMatcher) =
        oldMatcher.addClauses(goal.facts.predConj,
                              addedClauses,
                              goal.mayAlias,
                              goal.reduceWithFacts,
                              (MatchFunctions.isIrrelevantInstance(_, voc, _,
                                                                   reverseProp)),
                              reverseProp,
                              collector, order)
    
      val newCF = cf.updateQuantifierClauses(eager, newMatcher)
    
      val newTasks =
        if (collector.isLogging)
          // if we are producing proofs, we have to treat the instances
          // separately (to log all performed simplifications)
          for (f <- instances; t <- goal formulaTasks f) yield t
        else
          for (t <- goal.formulaTasks(Conjunction.disj(instances, order)))
            yield t
          
      (newCF, newTasks)
    }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new NegLitClauseTask(f, age, predicateMatchConfig)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    NegLitClauseTask.isCoveredFormula(f, predicateMatchConfig)

  val name : String = "NegLitClause"

}
