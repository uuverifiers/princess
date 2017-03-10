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
import ap.terfor.{ConstantTerm, Term, Formula, TermOrder}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

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
   * Determine the argument and result types of the function.
   */
  def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort)

  /**
   * Determine the argument and result types of the function.
   */
  def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort)

  /**
   * Determine the sort of function results.
   */
  def iResultSort(arguments : Seq[ITerm]) : Sort

  /**
   * Determine the sort of function results.
   */
  def resultSort(arguments : Seq[Term]) : Sort

  /**
   * Encode the function as a sorted predicate.
   */
  def toPredicate : SortedPredicate
}

/**
 * Class for monomorphically sorted functions.
 */
class MonoSortedIFunction(_name : String,
                          val argSorts : Seq[Sort],
                          val resSort : Sort,
                          _partial : Boolean, _relational : Boolean)
      extends SortedIFunction(_name, argSorts.size, _partial, _relational) {

  /**
   * Determine the argument and result types of the function.
   */
  def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) =
    (argSorts, resSort)

  /**
   * Determine the argument and result types of the function.
   */
  def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) =
    (argSorts, resSort)

  /**
   * Determine the sort of function results.
   */
  def iResultSort(arguments : Seq[ITerm]) : Sort = resSort

  /**
   * Determine the sort of function results.
   */
  def resultSort(arguments : Seq[Term]) : Sort = resSort

  /**
   * Encode the function as a sorted predicate.
   */
  def toPredicate : SortedPredicate =
    new MonoSortedPredicate(name, argSorts ++ List(resSort)) {
      override def sortConstraints(arguments : Seq[Term])
                                  (implicit order : TermOrder) : Formula =
        resSort membershipConstraint arguments.last
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * General class representing sorted predicates; sub-classes can model
 * both monomorphic and polymorphic predicates.
 */
abstract class SortedPredicate(_name : String, _arity : Int)
         extends Predicate(_name, _arity) {

  /**
   * Determine the argument types of the predicate.
   */
  def iArgumentTypes(arguments : Seq[ITerm]) : Seq[Sort]

  /**
   * Determine the argument types of the predicate.
   */
  def argumentTypes(arguments : Seq[Term]) : Seq[Sort]

  /**
   * Given argument terms of the predicate, determine constraints on the
   * range of the arguments that are implied by the predicate. E.g., for a
   * predicate encoding a function, such constraints would be derived from
   * the sort of the result sort.
   */
  def sortConstraints(arguments : Seq[Term])
                     (implicit order : TermOrder) : Formula

}

/**
 * Class for monomorphically sorted predicates
 */
class MonoSortedPredicate(_name : String,
                          val argSorts : Seq[Sort])
         extends SortedPredicate(_name, argSorts.size) {

  /**
   * Determine the argument types of the predicate.
   */
  def iArgumentTypes(arguments : Seq[ITerm]) : Seq[Sort] = argSorts

  /**
   * Determine the argument types of the predicate.
   */
  def argumentTypes(arguments : Seq[Term]) : Seq[Sort] = argSorts

  /**
   * Given argument terms of the predicate, determine constraints on the
   * range of the arguments that are implied by the predicate. E.g., for a
   * predicate encoding a function, such constraints would be derived from
   * the sort of the result sort.
   */
  def sortConstraints(arguments : Seq[Term])
                     (implicit order : TermOrder) : Formula =
    Conjunction.TRUE

}