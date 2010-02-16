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

package ap.proof.goal

import ap.basetypes.IdealInt
import ap.terfor.TermOrder
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
      extends ((LinearCombination, LinearCombination) => Boolean) {

  private val cache =
    new LRUCache[(LinearCombination, LinearCombination), Boolean] (10000)
  
  private def cacheKey(a : LinearCombination, b : LinearCombination) =
    if (Seqs.lexCombineInts(a.hashCode - b.hashCode, order.compare(a, b)) < 0)
      (a, b)
    else 
      (b, a)
  
  def apply(a : LinearCombination, b : LinearCombination) : Boolean =
    a == b || cache(cacheKey(a, b)) {
      !cf.diffIsShieldingLC(a, b, bc) && {
        val diff =
          LinearCombination.sum(Array((IdealInt.ONE, a), (IdealInt.MINUS_ONE, b)),
                                order)
        !reducer(EquationConj(diff, order)).isFalse
      }
    }

}
