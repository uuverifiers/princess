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

package ap.proof.goal;

import ap.terfor.{Term, Formula, ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, ConjunctEliminator}
import ap.terfor.substitutions.Substitution
import ap.parameters.Param
import ap.util.{Debug, FilterIt}
import ap.proof.tree.{ProofTree, ProofTreeFactory}

/**
 * Task for removing facts that are no longer needed (like equations that have
 * been applied to all other formulas), or that can be discharged directly by
 * moving them into the contraint.
 */
case object EliminateFactsTask extends EagerTask {

  val AC = Debug.AC_ELIM_FACTS_TASK

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val oldFacts = goal.facts
    val eliminator = new Eliminator(oldFacts, goal, ptf)
    val collector = goal.getInferenceCollector
    val newFacts = eliminator.eliminate(collector)
    
    ////////////////////////////////////////////////////////////////////////////
    
    if (newFacts == oldFacts && eliminator.divJudgements.isEmpty) {
      // nothing has changed and the application of this task was unnecessary
      ptf.updateGoal(goal)
    } else {
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(EliminateFactsTask.AC,
                      newFacts.isFalse ||
                      (newFacts.predConj.positiveLitsAsSet subsetOf
                          oldFacts.predConj.positiveLitsAsSet) &&
                      (newFacts.predConj.negativeLitsAsSet subsetOf
                          oldFacts.predConj.negativeLitsAsSet) &&
                      (newFacts.arithConj.positiveEqs.toSet subsetOf
                          oldFacts.arithConj.positiveEqs.toSet) &&
                      (newFacts.arithConj.negativeEqs.toSet subsetOf
                          oldFacts.arithConj.negativeEqs.toSet))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      // It can happen that new equalities can be inferred from the inequalities
      // after elimination, or that new inequalities occur. In this case, we
      // have to ensure that facts are normalised again, etc. This is done 
      // simply by generating a task to add the new equations or inequalities
      
      // TODO: this check can probably be optimised
      val factTasks =
        if (newFacts.isFalse ||
            newFacts.arithConj.inEqs.equalityInfs.isTrue &&
            (newFacts.arithConj.inEqs.toSet subsetOf
                oldFacts.arithConj.inEqs.toSet)) {
          List()
        } else {
          goal formulaTasks
            Conjunction.conj(newFacts.arithConj.inEqs, goal.order).negate
        }
      val divTasks =
        for (f <- eliminator.divJudgements; t <- goal formulaTasks f) yield t
      eliminator.postProcessor(ptf.updateGoal(newFacts, factTasks ++ divTasks,
                                              collector.getCollection, goal))
    }
  }

}


private class Eliminator(oriFacts : Conjunction,
                         goal : Goal, ptf : ProofTreeFactory)
              extends ConjunctEliminator(oriFacts,
                                         for (c <- goal.eliminatedConstants)
                                           yield c.asInstanceOf[Term],
                                         Param.GARBAGE_COLLECTED_FUNCTIONS(goal.settings),
                                         true,
                                         goal.order) {
  
  var postProcessor : ProofTree => ProofTree = ((p) => p)

  var divJudgements : List[Conjunction] = List()
  
  protected def nonUniversalElimination(f : Conjunction) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.weaken(pt, goal definedSyms f, goal.vocabulary))
  
  protected def universalElimination(eliminatedConstant : ConstantTerm,
                                     witness : (Substitution, TermOrder) => Substitution) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.eliminatedConstant(pt, eliminatedConstant,
                                                witness, goal.vocabulary))

  protected def addDivisibility(f : Conjunction) =
    divJudgements = f :: divJudgements

  private val taskInfoConstants = goal.tasks.taskInfos.constants
  private val compoundFormulaConstants = goal.compoundFormulas.constants
  
  protected def eliminationCandidates(facts : Conjunction) : Iterator[Term] =
    FilterIt((goal.order sort facts.constants).iterator,
             (c:ConstantTerm) => !(taskInfoConstants contains c) &&
                                 !(compoundFormulaConstants contains c))

}
