/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.types

import ap.parser.{IFunction, ITerm}
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate

/**
 * Sorted version of constants.
 */
class SortedConstantTerm(_name : String, val sort : Sort)
      extends ConstantTerm(_name) {
  override def clone : SortedConstantTerm =
    new SortedConstantTerm(name, sort)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * General class representing sorted functions; sub-classes can model
 * both monomorphic and polymorphic functions.
 */
abstract class SortedIFunction(_name : String, _arity : Int,
                               _partial : Boolean, _relational : Boolean)
         extends IFunction(_name, _arity, _partial, _relational) {
  /**
   * Method to determine the argument and result types of the function.
   */
  def functionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort)

  /**
   * Method to determine the sort of function results.
   */
  def resultSort(arguments : Seq[ITerm]) : Sort
}

class MonoSortedIFunction(_name : String,
                          val argTypes : Seq[Sort],
                          val resSort : Sort,
                          _partial : Boolean, _relational : Boolean)
      extends SortedIFunction(_name, argTypes.size, _partial, _relational) {

  def functionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) =
    (argTypes, resSort)

  def resultSort(arguments : Seq[ITerm]) : Sort = resSort
}