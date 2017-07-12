/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parser.{ITerm, IFormula, IExpression, IFunction}
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
                  Map(), order, List(), Set())

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            order : TermOrder,
            domainPredicates : Set[Predicate]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  Map(), order, List(), domainPredicates)

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder,
            domainPredicates : Set[Predicate]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, List(), domainPredicates)

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder,
            theories : Seq[Theory],
            domainPredicates : Set[Predicate]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, theories, domainPredicates)
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
                         val theories : Seq[Theory],
                         val domainPredicates : Set[Predicate]) {
  def updateOrder(newOrder : TermOrder) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, predicateMatchConfig, newOrder, theories,
                  domainPredicates)
  def updatePredicateMatchConfig(
                  newPredicateMatchConfig : Signature.PredicateMatchConfig) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, newPredicateMatchConfig, order, theories,
                  domainPredicates)

  def addTheories(additionalTheories : Seq[Theory],
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
                newTheories,
                domainPredicates)
    }

  /**
   * Check whether any of the symbols stored in this signature uses sorts
   * as defined in <code>ap.types</code>.
   */
  def isSorted : Boolean =
    (order.orderedConstants exists (_.isInstanceOf[ap.types.SortedConstantTerm])) ||
    (order.orderedPredicates exists (_.isInstanceOf[ap.types.SortedPredicate]))
}
