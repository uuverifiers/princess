/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.preds.Predicate
import ap.theories.Theory
import ap.util.Debug

object Signature {
  private val AC = Debug.AC_SIGNATURE

  object PredicateMatchStatus extends Enumeration {
    val Positive, Negative, None = Value
  }
  
  type PredicateMatchConfig = Map[Predicate, PredicateMatchStatus.Value]
  
  //////////////////////////////////////////////////////////////////////////////

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            order : TermOrder) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  Map(), order, List())

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, List())

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder,
            theories : Seq[Theory]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, theories)
}

/**
 * Helper class for storing the sets of declared constants (of various kinds)
 * and functions, together with the chosen <code>TermOrder</code>.
 */
class Signature private (val universalConstants : Set[ConstantTerm],
                         val existentialConstants : Set[ConstantTerm],
                         val nullaryFunctions : Set[ConstantTerm],
                         val predicateMatchConfig : Signature.PredicateMatchConfig,
                         val order : TermOrder,
                         val theories : Seq[Theory]) {
  def updateOrder(newOrder : TermOrder) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, predicateMatchConfig, newOrder, theories)

  def addTheories(additionalTheories : scala.collection.Seq[Theory],
                  front : Boolean = false) : Signature =
    if (additionalTheories.isEmpty) {
      this
    } else {
      val newTheories =
        if (front)
          additionalTheories ++ this.theories
        else
          this.theories ++ additionalTheories

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(Signature.AC, newTheories.toSet.size == newTheories.size)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      Signature(this.universalConstants,
                this.existentialConstants,
                this.nullaryFunctions,
                this.predicateMatchConfig ++ (
                  for (t <- additionalTheories.iterator;
                       p <- t.predicateMatchConfig.iterator) yield p),
                (this.order /: additionalTheories) { case (o, t) => t extend o },
                newTheories.toSeq)
    }

  /**
   * Check whether any of the symbols stored in this signature uses sorts
   * as defined in <code>ap.types</code>.
   */
  def isSorted : Boolean =
    (order.orderedConstants exists (_.isInstanceOf[ap.types.SortedConstantTerm])) ||
    (order.orderedPredicates exists (_.isInstanceOf[ap.types.SortedPredicate]))
}
