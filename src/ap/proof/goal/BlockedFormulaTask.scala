/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2017 Philipp Ruemmer <ph_r@gmx.net>
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

      if (!Seqs.disjoint(defSyms, goal.tasks.taskInfos.constants) ||
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