/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.{Formula, TermOrder, ComputationLogger}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj, Predicate}
import ap.terfor.inequalities.InEqConj
import ap.util.{Debug, Seqs, Logic}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.parameters.Param

import scala.collection.mutable.ArrayBuffer

object AddFactsTask {
  
  private val AC = Debug.AC_COMPLEX_FORMULAS_TASK

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  def isCoveredFormula(f : Conjunction) : Boolean =
    !f.isFalse &&
    (f.isTrue || f.isLiteral ||
     (f.isNegatedConjunction && f.negatedConjs(0).negatedConjs.isEmpty)) && 
    f.quans.isEmpty

  def extractFacts(t : Task) : Conjunction = t match {
    case t : AddFactsTask => {
      val formula = t.formula
      if (formula.isTrue) {
        Conjunction.FALSE
      } else if (formula.isLiteral) {
        Conjunction.negate(formula, formula.order)
      } else {
        //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
        Debug.assertInt(AddFactsTask.AC, formula.isNegatedConjunction)
        //-END-ASSERTION-/////////////////////////////////////////////////////////

        val disj = formula.negatedConjs(0)
        //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
        // possibly existing quantifiers should have been pulled out and
        // should not occur at this point
        Debug.assertInt(AddFactsTask.AC,
                        disj.quans.isEmpty && disj.negatedConjs.isEmpty)
        //-END-ASSERTION-/////////////////////////////////////////////////////////
            
        // the literals of the negated conjunction can be added as facts to
        // the goal
        disj
      }
    }
  }
  
  private object TRUE_EXCEPTION extends Exception
  
}

class AddFactsTask(_formula : Conjunction, _age : Int)
      extends FormulaTask(_formula, _age) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AddFactsTask.AC, !formula.isFalse)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val priority : Int = age - 20000
  
  /**
   * Perform the actual task (whatever needs to be done with <code>formula</code>)
   */
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {

    // dequeue all <code>AddFactsTask</code>s that are currently waiting
    val (newTaskManager, addTasks) =
      goal.tasks dequeueWhile (_.isInstanceOf[AddFactsTask])
    
    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)
    val order = goal.order
    
    val allFacts = new ArrayBuffer[Formula]
    allFacts += goal.facts
    
    var hasPreds = false
    
    def addNewFacts(facts : Conjunction) =
      if (facts.isFalse) {
        throw AddFactsTask.TRUE_EXCEPTION
      } else {
        if (!facts.predConj.isTrue)
          hasPreds = true
          
        if (proofs) {
          // when constructing proofs, we decompose conjunctions of inequalities
          // so that all computations concerning the new inequalities can be
          // recorded
          allFacts += facts.updateInEqs(InEqConj.TRUE)(order)
          for (lc <- facts.arithConj.inEqs)
            allFacts += InEqConj(lc, order)
        } else {
          allFacts += facts
        }
      }
    
    try {
      
      addNewFacts(AddFactsTask extractFacts this)
    
      for (t <- addTasks) {
        if (!(this eq t))
          addNewFacts(AddFactsTask extractFacts t)
      }
    
      val collector = goal.getInferenceCollector
      val updatedFacts = Conjunction(List(), allFacts.iterator, collector, order)
      
      val newTasks =
        if (hasPreds || !goal.compoundFormulas.lazyQuantifiedClauses.isEmpty)
          LazyMatchTask addTask goal
        else
          List()
      ptf.updateGoal(updatedFacts, newTaskManager ++ newTasks,
                     collector.getCollection, goal)
      
    } catch {
      case AddFactsTask.TRUE_EXCEPTION => ptf.updateGoal(Conjunction.FALSE, goal)
    }
  }
  
  /**
   * Create a new <code>FormulaTask</code> by updating the value of
   * <code>formula</code>
   */
  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new AddFactsTask(f, age)

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean =
    AddFactsTask.isCoveredFormula(f)

  val name : String = "AddFacts"

}
