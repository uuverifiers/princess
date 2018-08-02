/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.proof._
import ap.basetypes.IdealInt
import ap.terfor.{TermOrder, AliasStatus, AliasChecker}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithNegEqs}
import ap.terfor.conjunctions.ReduceWithConjunction
import ap.terfor.preds.Atom
import ap.util.{Debug, LRUCache, Seqs}

object AliasAnalyser {
  
  private val AC = Debug.AC_ALIAS_ANALYSER

}

/**
 * Class to approximate whether two terms have to be considered as potential
 * aliases, i.e., may have the same value. Two criteria are taken into account
 * for this: arithmetic facts that are available in a proof goal, and constant
 * freedom. The class does caching to speed up queries.
 */
class AliasAnalyser (reducer : ReduceWithConjunction,
                     cf : ConstantFreedom, bc : BindingContext,
                     order : TermOrder)
      extends AliasChecker {

  import AliasAnalyser._

  private val cache, cacheFD =
    new LRUCache[(LinearCombination, LinearCombination),
                 AliasStatus.Value] (10000)
  
  private def cacheKey(a : LinearCombination, b : LinearCombination) = {
    val aHash = a.hashCode
    val bHash = b.hashCode
    if (aHash < bHash || (aHash == bHash && order.compare(a, b) < 0))
      (a, b)
    else
      (b, a)
  }
  
  /**
   * Check whether two terms have to be considered as potential
   * aliases, i.e., may have the same value.
   */
  def apply(a : LinearCombination, b : LinearCombination,
            includeCannotDueToFreedom : Boolean) : AliasStatus.Value = ap.util.Timer.measure("AliasAnalyser") {
    if (includeCannotDueToFreedom) {
      checkAliasFD(a, b)
    } else {
      val res = checkAlias(a, b)
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC, res == (checkAliasFD(a, b) match {
                                     case AliasStatus.CannotDueToFreedom =>
                                       AliasStatus.Cannot
                                     case s => s
                                   }))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
  }

  /**
   * Check whether the given terms can be aliased.
   */
  private def checkAlias(a : LinearCombination,
                         b : LinearCombination) : AliasStatus.Value =
    if (a == b) {
      AliasStatus.Must
    } else /* cache(cacheKey(a, b)) */ {
      if (cf.diffIsShieldingLC(a, b, bc)) {
        AliasStatus.Cannot
      } else ap.util.Timer.measure("AliasAnalyser - reduction") {
        implicit val o = order
        val reduced = reducer(EquationConj(a - b, order))
        
        if (reduced.isTrue)
          AliasStatus.Must
        else if (reduced.isFalse)
          AliasStatus.Cannot
        else
          AliasStatus.May
      }
    }

  /**
   * Check whether the given terms can be aliased, and also produce
   * the result <code>AliasStatus.CannotDueToFreedom</code>
   */
  private def checkAliasFD(a : LinearCombination,
                           b : LinearCombination) : AliasStatus.Value =
    if (a == b)
      AliasStatus.Must
    else cacheFD(cacheKey(a, b)) {
      implicit val o = order
      val reduced = reducer(EquationConj(a - b, order))
      
      if (reduced.isTrue)
        AliasStatus.Must
      else if (reduced.isFalse)
        AliasStatus.Cannot
      else if (cf.diffIsShieldingLC(a, b, bc))
        AliasStatus.CannotDueToFreedom
      else
        AliasStatus.May
    }

  /**
   * Find atoms within the sequence <code>atoms</code> that may
   * alias with atoms with the given <code>arguments</code>
   * as the first arguments.
   */
  def findMayAliases(atoms : Seq[Atom],
                     arguments : Seq[LinearCombination],
                     includeCannotDueToFreedom : Boolean)
                   : Map[AliasStatus.Value, Seq[Atom]] = {
    val N = arguments.size
    atoms groupBy { a =>
      var res = AliasStatus.May
      var n = 0
      
      while (n < N && res != AliasStatus.Cannot)
        apply(a(n), arguments(n),
              includeCannotDueToFreedom &&
              res != AliasStatus.CannotDueToFreedom) match {
          case AliasStatus.Must | AliasStatus.May =>
            // nothing
          case s =>
            res = s
        }

      res
    }
  }

}
