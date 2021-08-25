/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.Signature.PredicateMatchConfig
import ap.proof._
import ap.terfor.{TermOrder, Sorted, Formula, ConstantTerm}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions,
                               IterativeClauseMatcher}
import ap.util.{Debug, Seqs}

object CompoundFormulas {
  
  private val AC = Debug.AC_GOAL
  
  def EMPTY(config : PredicateMatchConfig) =
    new CompoundFormulas(NegatedConjunctions.TRUE,
                         IterativeClauseMatcher.empty(true, config),
                         IterativeClauseMatcher.empty(false, config))
  
}

case class CompoundFormulas(qfClauses : NegatedConjunctions,
                            eagerQuantifiedClauses : IterativeClauseMatcher,
                            lazyQuantifiedClauses : IterativeClauseMatcher)
           extends Sorted[CompoundFormulas] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(CompoundFormulas.AC,
                   !qfClauses.containsLiteral &&
                   !qfClauses.containsNegatedConjunction &&
                   qfClauses.variables.isEmpty &&
                   qfClauses.predicates.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def updateQFClauses(newQFClauses : NegatedConjunctions) =
    if (qfClauses eq newQFClauses)
      this
    else
      CompoundFormulas(newQFClauses, eagerQuantifiedClauses, lazyQuantifiedClauses)
  
  def quantifierClauses(eager : Boolean) =
    if (eager) eagerQuantifiedClauses else lazyQuantifiedClauses
  
  def updateQuantifierClauses(eager : Boolean, newClauses : IterativeClauseMatcher) =
    if (eager) {
      if (eagerQuantifiedClauses eq newClauses)
        this
      else
        CompoundFormulas(qfClauses, newClauses, lazyQuantifiedClauses)
    } else {
      if (lazyQuantifiedClauses eq newClauses)
        this
      else
        CompoundFormulas(qfClauses, eagerQuantifiedClauses, newClauses)
    }
  
  def isEmpty =
    qfClauses.isEmpty &&
    eagerQuantifiedClauses.clauses.isEmpty &&
    lazyQuantifiedClauses.clauses.isEmpty
  
  def isFalse =
    qfClauses.isFalse ||
    eagerQuantifiedClauses.clauses.isFalse ||
    lazyQuantifiedClauses.clauses.isFalse
  
  def sortBy(order : TermOrder) : CompoundFormulas =
    CompoundFormulas(qfClauses sortBy order,
                     eagerQuantifiedClauses sortBy order,
                     lazyQuantifiedClauses sortBy order)
  
  def isSortedBy(order : TermOrder) : Boolean =
    (qfClauses isSortedBy order) &&
    (eagerQuantifiedClauses isSortedBy order) &&
    (lazyQuantifiedClauses isSortedBy order)

  lazy val constants : Set[ConstantTerm] =
    qfClauses.constants ++ constantsInMatchedClauses
  
  lazy val constantsInMatchedClauses : Set[ConstantTerm] =
    eagerQuantifiedClauses.clauses.constants ++
    lazyQuantifiedClauses.clauses.constants
  
  lazy val predicates : Set[Predicate] =
    eagerQuantifiedClauses.clauses.predicates ++
    lazyQuantifiedClauses.clauses.predicates
  
  //////////////////////////////////////////////////////////////////////////////

  def updateConstantFreedom(cf : ConstantFreedom, goal : Goal)
                           : (Seq[PrioritisedTask], CompoundFormulas) = {

    // handle qf-clauses

    def illegalQFClause(c : Conjunction) =
      (!Seqs.disjoint(c.constants, goal.eliminatedConstants) ||
       !Conjunction.collectQuantifiers(c).isEmpty) &&
      !cf.isShielded(c, goal.bindingContext)
    
    // handle matched clauses: rematch literals and clauses that contain
    // constants whose freedom has changed
    
    val changedConsts = goal.constantFreedom changedConstants cf
    def changedFormula(f : Formula) = !Seqs.disjoint(changedConsts, f.constants)

    val newVocabulary = goal.vocabulary.updateConstantFreedom(cf)
    
    val (newTasks, newCF) =
      map(_ partition (illegalQFClause _),
          _ remove (changedFormula _),
          Goal.formulaTasks(_, goal.age,
                            goal.eliminatedConstants, newVocabulary, goal.settings),
          goal.order)
    
    val matchTask =
      if (goal.facts.predConj.isTrue) List() else (LazyMatchTask addTask goal)
    (newTasks ++ matchTask, newCF)
  }

  /**
   * @param qfClauseMapping map the qf-clauses to a set of clauses that is
   *                        supposed to be turned
   *                        into tasks, and a set that is supposed to be kept
   */
  def mapQFClauses(qfClauseMapping : (NegatedConjunctions) =>
                                       (Seq[Conjunction], Seq[Conjunction]),
                   taskifier :       (Conjunction) => Seq[FormulaTask],
                   order :           TermOrder)
                  : (Seq[PrioritisedTask], CompoundFormulas) = {
    val (otherStuff, realClauses) = qfClauseMapping(this.qfClauses)
    val newClauses =
      if (Seqs.identicalSeqs(realClauses, this.qfClauses))
        this.qfClauses
      else
        NegatedConjunctions(realClauses, order)

    val newTasks = for (c <- otherStuff; t <- taskifier(c)) yield t

    (newTasks, updateQFClauses(newClauses))
  }

  /**
   * @param qfClauseMapping map the qf-clauses to a set of clauses that is
   *                        supposed to be turned
   *                        into tasks, and a set that is supposed to be kept
   * @param matcherMapping  map the matchers to a set of formulas that is
   *                        supposed to be turned into tasks, and a new matcher
   */
  private def map(qfClauseMapping : (NegatedConjunctions) =>
                                    (Seq[Conjunction], Seq[Conjunction]),
                  matcherMapping :  (IterativeClauseMatcher) =>
                                    (Seq[Conjunction], IterativeClauseMatcher),
                  taskifier :       (Conjunction) => Seq[FormulaTask],
                  order :           TermOrder)
                 : (Seq[PrioritisedTask], CompoundFormulas) = {
    // map qf-clauses

    val (otherStuff, realClauses) = qfClauseMapping(this.qfClauses)
    val newClauses = this.qfClauses.update(realClauses, order)

    val newTasks = for (c <- otherStuff; t <- taskifier(c)) yield t
    
    // map the matchers
  
    val (removedEagerClauses, newEagerClauses) =
      matcherMapping(eagerQuantifiedClauses)
    val (removedLazyClauses, newLazyClauses) =
      matcherMapping(lazyQuantifiedClauses)

    val eagerClausesTasks =
      for (c <- removedEagerClauses; t <- taskifier(c)) yield t
    val lazyClausesTasks =
      for (c <- removedLazyClauses; t <- taskifier(c)) yield t
    
    (newTasks ++ eagerClausesTasks ++ lazyClausesTasks,
     if ((newClauses eq this.qfClauses) &&
         (newEagerClauses eq eagerQuantifiedClauses) &&
         (newLazyClauses eq lazyQuantifiedClauses))
       this
     else
       CompoundFormulas(newClauses, newEagerClauses, newLazyClauses))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  override def toString : String =
    "(" + qfClauses + ", " +
          eagerQuantifiedClauses.clauses + ", " +
          lazyQuantifiedClauses.clauses + ")"
}
