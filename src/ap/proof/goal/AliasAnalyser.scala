/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

  private val cache =
    new LRUCache[(LinearCombination, LinearCombination), AliasStatus.Value] (10000)
  
  private def cacheKey(a : LinearCombination, b : LinearCombination) = {
    val aHash = a.hashCode
    val bHash = b.hashCode
    if (aHash < bHash || (aHash == bHash && order.compare(a, b) < 0))
      (a, b)
    else
      (b, a)
  }
  
  def apply(a : LinearCombination, b : LinearCombination) : AliasStatus.Value =
    if (a == b) {
      AliasStatus.Must
    } else cache(cacheKey(a, b)) {
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

}
