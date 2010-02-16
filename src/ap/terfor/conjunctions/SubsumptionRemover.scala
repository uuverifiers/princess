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

package ap.terfor.conjunctions;

/**
 * Naive version of a subsumption test
 */
class SubsumptionRemover(order : TermOrder) {

  private val disjuncts = new scala.collection.mutable.HashSet[Conjunction]

  def result : Conjunction = Conjunction.disj(disjuncts, order)
  
  def addDisjuncts(c : Conjunction) : Unit = addDisjuncts(c, Conjunction.TRUE)

  def addDisjuncts(c : Conjunction, conjunct : Conjunction) : Unit =
    if (!c.quans.isEmpty ||
        c.negatedConjs.size != 1 || !c.negatedConjs(0).quans.isEmpty) {
      addDisjunct(Conjunction.conj(Array(c, conjunct), order))
    } else {
      // then there is a single negated conjunction, i.e., disjunction, that
      // we iterate over
      val disj = c.negatedConjs(0)
      val cWithoutDisj = c.updateNegatedConjs(NegatedConjunctions.TRUE)(order)
      val newConjunct = Conjunction.conj(Array(conjunct, cWithoutDisj), order)
      
      for (d <- disj.updateNegatedConjs(NegatedConjunctions.TRUE)(order).elements)
        addDisjunct(Conjunction.conj(Array(d.negate, newConjunct), order))
      for (d <- disj.negatedConjs)
        addDisjuncts(d, newConjunct)
    }

  private def addDisjunct(c : Conjunction) : Unit =
    if (!(disjuncts exists (c implies _))) {
      disjuncts retain ((d) => !(d implies c))
      disjuncts += c
    }
  
}
