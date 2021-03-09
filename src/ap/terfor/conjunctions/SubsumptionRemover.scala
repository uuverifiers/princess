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

package ap.terfor.conjunctions;

import ap.terfor._

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
      
      for (d <- disj.updateNegatedConjs(NegatedConjunctions.TRUE)(order).iterator)
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
