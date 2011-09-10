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

package ap.proof;

import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, SubsumptionRemover}
import ap.proof.goal.Goal
import ap.proof.tree.TestProofTree
import ap.parameters.{GoalSettings, Param}
import ap.util.{Debug, Seqs, LRUCache, Timeout}

object ConstraintSimplifier {
  
  val AC = Debug.AC_CONSTRAINT_SIMPLIFIER  
  
  def apply(lemmas : Boolean, ground2DNF : Boolean, output : Boolean) =
    (lemmas, ground2DNF, output) match {
      case (false, true, false) => FAIR_SIMPLIFIER
      case (false, true, true) => FAIR_SIMPLIFIER_TRACE
      case (true, true, false) => LEMMA_SIMPLIFIER
      case (true, true, true) => LEMMA_SIMPLIFIER_TRACE
      case (false, false, false) => FAIR_SIMPLIFIER_NON_DNF
      case (false, false, true) => FAIR_SIMPLIFIER_TRACE_NON_DNF
      case (true, false, false) => LEMMA_SIMPLIFIER_NON_DNF
      case (true, false, true) => LEMMA_SIMPLIFIER_TRACE_NON_DNF
    }
  
  val NO_SIMPLIFIER : ConstraintSimplifier = new ConstraintSimplifier {
    def apply(f : Conjunction, order : TermOrder) : Conjunction = f
    def canHandle(f : Conjunction) : Boolean = true
  }
  
  lazy val FAIR_SIMPLIFIER : ConstraintSimplifier =
    new SimpleSimplifier(false, true, false)
  lazy val FAIR_SIMPLIFIER_TRACE : ConstraintSimplifier =
    new SimpleSimplifier(false, true, true)
  lazy val LEMMA_SIMPLIFIER : ConstraintSimplifier =
    new SimpleSimplifier(true, true, false)
  lazy val LEMMA_SIMPLIFIER_TRACE : ConstraintSimplifier =
    new SimpleSimplifier(true, true, true)

  lazy val FAIR_SIMPLIFIER_NON_DNF : ConstraintSimplifier =
    new SimpleSimplifier(false, false, false)
  lazy val FAIR_SIMPLIFIER_TRACE_NON_DNF : ConstraintSimplifier =
    new SimpleSimplifier(false, false, true)
  lazy val LEMMA_SIMPLIFIER_NON_DNF : ConstraintSimplifier =
    new SimpleSimplifier(true, false, false)
  lazy val LEMMA_SIMPLIFIER_TRACE_NON_DNF : ConstraintSimplifier =
    new SimpleSimplifier(true, false, true)

}

abstract class ConstraintSimplifier {
  /**
   * Simplify the formula <code>f</code>
   */
  def apply(f : Conjunction, order : TermOrder) : Conjunction
  
  def canHandle(f : Conjunction) : Boolean
}

class SimpleSimplifier(lemmas : Boolean, ground2DNF : Boolean, output : Boolean)
      extends ConstraintSimplifier {
  
  private lazy val posProver =
    new ExhaustiveProver(false,
                         Param.CONSTRAINT_SIMPLIFIER.set(
                         Param.FULL_SPLITTING.set(GoalSettings.DEFAULT, false),
                           ConstraintSimplifier.NO_SIMPLIFIER))
  private lazy val negProver =
    new ExhaustiveProver(false,
                         Param.CONSTRAINT_SIMPLIFIER.set(
                         Param.FULL_SPLITTING.set(GoalSettings.DEFAULT, ground2DNF),
                           ConstraintSimplifier.NO_SIMPLIFIER))

  private def print(str : => String) : Unit = (if (output) Predef.print(str))
  private def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  private val EMPTY : Set[Quantifier]  = Set()
  private val ALL : Set[Quantifier]    = Set(Quantifier.ALL)
  private val EX : Set[Quantifier]     = Set(Quantifier.EX)
  private val ALL_EX : Set[Quantifier] = Set(Quantifier.EX, Quantifier.ALL)
    
  def canHandle(f : Conjunction) : Boolean = collectQuantifiers(f) != ALL_EX

  private val cache = new LRUCache[Conjunction, Conjunction] (1000)
  
  def apply(f : Conjunction, order : TermOrder) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConstraintSimplifier.AC, order isSortingOf f)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    cache(f) {
      collectQuantifiers(f) match {
      case ALL => simplify(f, order)
      case EX => negSimplify(f, order)
      case EMPTY =>
        if (ground2DNF && f.size > 1)
          negSimplify(f, order)
        else
          f
      }
    }
  }
  
  private def simplify(f : Conjunction, order : TermOrder) : Conjunction =
    Timeout.unfinishedValue(None) {
      println("Simplify: " + f + " (positive)")
      val res = if (lemmas) {
        QuantifierElimProver(f, false, order)
      } else {
        val tree = posProver(f, order)
        TestProofTree.assertNormalisedTree(tree)
        tree.closingConstraint
      }
      println("          " + res)
      res
    }

  private def negSimplify(f : Conjunction, order : TermOrder) : Conjunction =
    Timeout.unfinishedValue(None) {
      println("Simplify: " + f + " (negative)")
      val res = if (lemmas) {
        QuantifierElimProver(f.negate, ground2DNF, order).negate
      } else {
        val tree = negProver(f.negate, order)
        TestProofTree.assertNormalisedTree(tree)
        tree.closingConstraint.negate
      }
      println("          " + res)
      res
    }
  
  private def collectQuantifiers(f : Formula) : Set[Quantifier] =
    Conjunction.collectQuantifiers(f, (conj) =>
           Set() ++ conj.quans.drop(1) ++
           // we only look for proper divisibility (not divisibility by one ...)
           (if (conj.isProperDivisibility)
              Set()
            else
              Set(conj.quans(0))))
  
}
