/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof;

import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, SubsumptionRemover,
                               ReduceWithConjunction}
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
  
  def apply(rawF : Conjunction, order : TermOrder) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConstraintSimplifier.AC, order isSortingOf rawF)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    cache.cached(rawF) {
      val f = ReduceWithConjunction(Conjunction.TRUE, order)(rawF)
      collectQuantifiers(f) match {
//      case ALL | EX if (!f.quans.isEmpty) => simplifyMiniScope(f, order)
      case ALL   => simplify(f, order)
      case EX    => negSimplify(f, order)
      case EMPTY =>
        if (ground2DNF && !isInDNF(f, false))
          negSimplify(f, order)
        else
          f
      }
    } {
      result =>
        // There is a small chance that we will get a result that is wrongly
        // sorted, since the <code>TermOrder</code> is not part of the cache
        // key. Therefore we sort the result properly in any case.
        result sortBy order
    }
  }

  private def isInDNF(c : Conjunction, negated : Boolean) : Boolean =
    if (negated)
      c.negatedConjs forall (isInDNF(_, false))
    else
      c.negatedConjs match {
        case Seq()  => true
        case Seq(d) => isInDNF(d, true)
        case _      => false
      }

  private def simplify(f : Conjunction, order : TermOrder) : Conjunction =
    Timeout.unfinishedValue(None) {
      println("Simplify: " + f + " (positive)")
      val res = if (lemmas) Console.withOut(ap.CmdlMain.NullStream) {
        QuantifierElimProver(f, false, order)
      } else {
        val tree = Console.withOut(ap.CmdlMain.NullStream) { posProver(f, order) }
        TestProofTree.assertNormalisedTree(tree)
        tree.closingConstraint
      }
      println("          " + res)
      res
    }

  private def negSimplify(f : Conjunction, order : TermOrder) : Conjunction =
    Timeout.unfinishedValue(None) {
      println("Simplify: " + f + " (negative)")
      val res = if (lemmas) Console.withOut(ap.CmdlMain.NullStream) {
        QuantifierElimProver(f.negate, ground2DNF, order).negate
      } else {
        val tree = Console.withOut(ap.CmdlMain.NullStream) { negProver(f.negate, order) }
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

  private def simplifyMiniScope(f : Conjunction, order : TermOrder) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConstraintSimplifier.AC, !f.quans.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (withoutQ, withQ) =
      f.iterator partition {
                  x => x.variables.isEmpty && collectQuantifiers(x).isEmpty }
    val withQList = withQ.toList

    val subres =
      if (withQList.size == 1 && withQList.head.isNegatedConjunction) {
          simplifyMiniScope(Conjunction.quantify(for (q <- f.quans) yield q.dual,
                                   withQList.head.negatedConjs(0), order), order).negate
      } else {
        val withFor =
          Conjunction.quantify(f.quans, Conjunction.conj(withQList, order), order)
        f.quans.last match {
          case Quantifier.ALL => simplify(withFor, order)
          case Quantifier.EX  => negSimplify(withFor, order)
        }
      }

    Conjunction.conj((Iterator single subres) ++ withoutQ, order)
  }
  
}
