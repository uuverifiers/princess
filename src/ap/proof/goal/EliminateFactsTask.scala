/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.arithconj.ModelElement
import ap.terfor.{Term, Formula, ConstantTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, ConjunctEliminator}
import ap.terfor.substitutions.Substitution
import ap.parameters.Param
import ap.util.{Debug, FilterIt, LazyMappedSet}
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

      val factTasks =
        if (newFacts.isFalse ||
            (newFacts.arithConj.inEqs eq oldFacts.arithConj.inEqs)) {
          List()
        } else {
          val newInEqs =
            newFacts.arithConj.inEqs --
            oldFacts.arithConj.inEqs
          val newEqs =
            newFacts.arithConj.inEqs.equalityInfs --
            oldFacts.arithConj.inEqs.equalityInfs
          goal formulaTasks
            Conjunction.conj(List(newInEqs, newEqs), goal.order).negate
        }

      val divTasks =
        for (f <- eliminator.divJudgements; t <- goal formulaTasks f) yield t
      eliminator.postProcessor(ptf.updateGoal(newFacts, factTasks ++ divTasks,
                                              collector.getCollection, goal))
    }
  }

}


private object Eliminator {
  val constantTermFilter : PartialFunction[Term, ConstantTerm] = {
    case c : ConstantTerm => c
  }
}

private class Eliminator(oriFacts : Conjunction,
                         goal : Goal, ptf : ProofTreeFactory)
              extends ConjunctEliminator(oriFacts,
                                         new LazyMappedSet[ConstantTerm, Term](
                                           goal.eliminatedConstants,
                                           _.asInstanceOf[Term],
                                           Eliminator.constantTermFilter
                                         ),
//                                         for (c <- goal.eliminatedConstants)
//                                           yield c.asInstanceOf[Term],
                                         Param.GARBAGE_COLLECTED_FUNCTIONS(goal.settings),
                                         goal.order) {
  
  var postProcessor : ProofTree => ProofTree = ((p) => p)

  var divJudgements : List[Conjunction] = List()
  
  protected def nonUniversalElimination(f : Conjunction) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.weaken(pt, goal definedSyms f, goal.vocabulary))
  
  protected def universalElimination(m : ModelElement) =
    postProcessor = postProcessor compose
      ((pt:ProofTree) => ptf.eliminatedConstant(pt, m, goal.vocabulary))

  protected def addDivisibility(f : Conjunction) =
    divJudgements = f :: divJudgements

  private val taskConstants = goal.tasks.taskConstants
  private val compoundFormulaConstants = goal.compoundFormulas.constants
  
  protected def isEliminationCandidate(t : Term) : Boolean = t match {
    case c : ConstantTerm => !(taskConstants contains c) &&
                             !(compoundFormulaConstants contains c)
    case _ => false
  }

  private val fullElimCandidates =
    goal.order sort (
      oriFacts.constants -- taskConstants -- compoundFormulaConstants)

  protected def eliminationCandidates(facts : Conjunction) : Iterator[Term] =
    FilterIt(fullElimCandidates.iterator, facts.constants)
}
