/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parser.{ITerm, IFormula, IExpression, IFunction}
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.preds.Predicate
import ap.theories.Theory

object Signature {
  abstract class FunctionType {
    def argumentTypeGuard(args : Seq[ITerm]) : IFormula
    def resultTypeGuard  (res : ITerm)       : IFormula
  }
  
  object TopFunctionType extends FunctionType {
    import IExpression._
    def argumentTypeGuard(args : Seq[ITerm]) : IFormula = i(true)
    def resultTypeGuard  (res : ITerm)       : IFormula = i(true)
  }
  
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
                  Map(), order, List(), Set(), Map())

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            order : TermOrder,
            domainPredicates : Set[Predicate],
            functionTypes : Map[IFunction, Signature.FunctionType]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  Map(), order, List(), domainPredicates, functionTypes)

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder,
            domainPredicates : Set[Predicate],
            functionTypes : Map[IFunction, Signature.FunctionType]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, List(), domainPredicates, functionTypes)

  def apply(universalConstants : Set[ConstantTerm],
            existentialConstants : Set[ConstantTerm],
            nullaryFunctions : Set[ConstantTerm],
            predicateMatchConfig : PredicateMatchConfig,
            order : TermOrder,
            theories : Seq[Theory],
            domainPredicates : Set[Predicate],
            functionTypes : Map[IFunction, Signature.FunctionType]) =
    new Signature(universalConstants, existentialConstants, nullaryFunctions,
                  predicateMatchConfig, order, theories, domainPredicates, functionTypes)
}

/**
 * Helper class for storing the sets of declared constants (of various kinds)
 * and functions, together with the chosen <code>TermOrder</code>.
 */
class Signature(val universalConstants : Set[ConstantTerm],
                val existentialConstants : Set[ConstantTerm],
                val nullaryFunctions : Set[ConstantTerm],
                val predicateMatchConfig : Signature.PredicateMatchConfig,
                val order : TermOrder,
                val theories : Seq[Theory],
                val domainPredicates : Set[Predicate],
                val functionTypes : Map[IFunction, Signature.FunctionType]) {
  def updateOrder(newOrder : TermOrder) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, predicateMatchConfig, newOrder, theories,
                  domainPredicates, functionTypes)
  def updatePredicateMatchConfig(
                  newPredicateMatchConfig : Signature.PredicateMatchConfig) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, newPredicateMatchConfig, order, theories,
                  domainPredicates, functionTypes)
  def updateFunctionTypes(newFunctionTypes : Map[IFunction, Signature.FunctionType]) =
    new Signature(universalConstants, existentialConstants,
                  nullaryFunctions, predicateMatchConfig, order, theories,
                  domainPredicates, newFunctionTypes)
}
