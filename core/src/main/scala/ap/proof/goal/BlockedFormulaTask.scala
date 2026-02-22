/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2022 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.ConstantTerm
import ap.terfor.equations.EquationConj
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.util.{Debug, Seqs}

object BlockedFormulaTask {

  private val AC = Debug.AC_BLOCKED_FORMULAS_TASK
  
  def isBlocked(f : Conjunction, goal : Goal) : Option[BlockedFormulaTask] =
    if (RegularityBlockedTask.isBlocked(f, goal))
      Some(new RegularityBlockedTask(f))
    else
      None

}

/**
 * Task for representing formulae whose application is currently
 * blocked. Such formulae are only stored for the time being, until
 * possibly at some later point they can be used (or discarded).
 */
abstract class BlockedFormulaTask(_formula : Conjunction)
         extends FormulaTask(_formula, 0) {

  val priority : Int = Int.MaxValue

  /**
   * Decide whether the given formula should still be blocked, or
   * be released at this point.
   */
  protected def releaseFormula(f : Conjunction, goal : Goal) : Boolean

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree =
    if (Param.APPLY_BLOCKED_TASKS(goal.settings)) {
      ptf.updateGoal(goal formulaTasks formula, goal)
    } else {
      // application has no actual effect
      ptf updateGoal goal
    }

  /**
   * Return <code>true</code> if <code>f</code> is a formula that can be handled
   * by this task
   */
  protected[goal] def isCoveredFormula(f : Conjunction) : Boolean = true

  /**
   * Update the task with possibly new information from the goal
   */
  override def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[FormulaTask] = {
    val reducedFormula = goal.reduceWithFacts.tentativeReduce(formula)

    if (releaseFormula(reducedFormula, goal)) {

      if (Param.PROOF_CONSTRUCTION(goal.settings))
        for (t <- goal formulaTasks formula;
             s <- t.constructWrappedTask(
                      goal.reduceWithFacts.tentativeReduce(t.formula),
                      goal))
        yield s
      else
        goal formulaTasks reducedFormula

    } else {

      if ((reducedFormula eq formula) ||
          Param.PROOF_CONSTRUCTION(goal.settings))
        List(this)
      else
        List(this.updateFormula(reducedFormula, goal))

    }
  }
}


////////////////////////////////////////////////////////////////////////////////


object RegularityBlockedTask {

  private val AC = Debug.AC_BLOCKED_FORMULAS_TASK
  
  def isBlocked(f : Conjunction, goal : Goal) : Boolean =
    f.quans.isEmpty && !f.arithConj.positiveEqs.isEmpty &&
    f.arithConj.inEqs.isTrue && f.predConj.isTrue && {

      val negEqs =
        if (f.arithConj.negativeEqs.size == 1 &&
            f.negatedConjs.isEmpty)
          f.arithConj.negativeEqs
        else if (f.arithConj.negativeEqs.isTrue && f.negatedConjs.size == 1 &&
                 f.negatedConjs(0).quans.isEmpty &&
                 f.negatedConjs(0).size == f.negatedConjs(0).arithConj.positiveEqs.size)
          f.negatedConjs(0).arithConj.positiveEqs
        else
          return false

      val allEqs = f.arithConj.positiveEqs ++ negEqs
      val defSyms =
        (for (lc <- allEqs) yield lc.leadingTerm.asInstanceOf[ConstantTerm]).toSet

      if (!Seqs.disjoint(defSyms, goal.tasks.taskConstants) ||
          !Seqs.disjoint(defSyms, goal.compoundFormulas.constants))
        return false

      val order = goal.order
      val eqs = Conjunction.conj(EquationConj(allEqs, order), order)
      goal.facts implies ReduceWithConjunction(eqs, order)(goal.facts)
    }

}


/**
 * Formulae of the shape
 * <code>t1 = 0 & ... & tn = 0  &  !(s1 = 0 & ... & sm = 0)</code>
 * that are blocked because the equations
 * <code>t1 = 0 & ... & tn = 0  &  s1 = 0 & ... & sm = 0</code>
 * would reduce the facts of a goal to a mere subset
 */
class RegularityBlockedTask(_formula : Conjunction)
      extends BlockedFormulaTask(_formula) {

  protected def releaseFormula(f : Conjunction, goal : Goal) : Boolean =
    AddFactsTask isCoveredFormula f

  protected[goal] def updateFormula(f : Conjunction, goal : Goal) : FormulaTask =
    new RegularityBlockedTask(f)

  val name : String = "RegularityBlocked"

}
