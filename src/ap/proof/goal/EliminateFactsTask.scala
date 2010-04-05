/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
    val eliminator = new Eliminator(goal.facts, goal, ptf)
    val collector = goal.getInferenceCollector
    val newFacts = eliminator.eliminate(collector)
    
    ////////////////////////////////////////////////////////////////////////////
    
    if (newFacts == goal.facts) {
      // nothing has changed and the application of this task was unnecessary
      ptf.updateGoal(goal)
    } else {
      
      // It can happen that new equalities can be inferred from the inequalities
      // after elimination. In this case, we have to ensure that facts are
      // normalised again, etc. This is done simply by generating a task
      // to add the new equations
        
      val newTasks =
        if (newFacts.arithConj.inEqs.equalityInfs.isTrue) {
          List()
        } else {
          goal formulaTasks
            Conjunction.conj(newFacts.arithConj.inEqs.equalityInfs, goal.order).negate
        }
      eliminator.postProcessor(ptf.updateGoal(newFacts, newTasks,
                                              collector.getCollection, goal))
    }
  }

}


private class Eliminator(oriFacts : Conjunction,
                         goal : Goal, ptf : ProofTreeFactory)
              extends ConjunctEliminator(oriFacts,
                                         for (c <- goal.eliminatedConstants)
                                           yield c.asInstanceOf[Term],
                                         goal.order) {
  
  var postProcessor : ProofTree => ProofTree = ((p) => p)

  protected def nonUniversalElimination(f : Conjunction) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.weaken(pt, goal definedSyms f, goal.vocabulary))
  
  protected def universalElimination(eliminatedConstant : ConstantTerm,
                                     witness : (Substitution, TermOrder) => Substitution) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.eliminatedConstant(pt, eliminatedConstant,
                                                witness, goal.vocabulary))

  private val taskInfoConstants = goal.tasks.taskInfos.constants
  private val compoundFormulaConstants = goal.compoundFormulas.constants
  
  protected def eliminationCandidates(facts : Conjunction) : Iterator[Term] =
    FilterIt((goal.order sort facts.constants).elements,
             (c:ConstantTerm) => !(taskInfoConstants contains c) &&
                                 !(compoundFormulaConstants contains c))

}
