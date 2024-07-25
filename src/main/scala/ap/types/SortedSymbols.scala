/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.types

import ap.parser.{IFunction, ITerm}
import ap.terfor.{ConstantTerm, Term, Formula, TermOrder}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object SortedConstantTerm {
  def sortOf(c : ConstantTerm) : Sort = c match {
    case c : SortedConstantTerm => c.sort
    case _ => Sort.Integer
  }
  def unapply(c : Term) : Option[(SortedConstantTerm, Sort)] = c match {
    case c : SortedConstantTerm => Some((c, c.sort))
    case _ => None
  }
}

/**
 * Sorted version of constants.
 */
class SortedConstantTerm(_name : String, val sort : Sort)
      extends ConstantTerm(_name) {
  override def clone : SortedConstantTerm =
    new SortedConstantTerm(name, sort)
}

////////////////////////////////////////////////////////////////////////////////

object SortedIFunction {

  /**
   * Determine the argument and result type of any function.
   */
  def functionType(fun : IFunction,
                   arguments : Seq[Term]) : (Seq[Sort], Sort) = fun match {
    case fun : SortedIFunction =>
      fun functionType arguments
    case _ =>
      (for (_ <- 0 until fun.arity) yield Sort.Integer, Sort.Integer)
  }

  /**
   * Determine the argument and result type of any function.
   */
  def iFunctionType(fun : IFunction,
                    arguments : Seq[ITerm]) : (Seq[Sort], Sort) = fun match {
    case fun : SortedIFunction =>
      fun iFunctionType arguments
    case _ =>
      (for (_ <- 0 until fun.arity) yield Sort.Integer, Sort.Integer)
  }

  /**
   * Determine the argument types of any function.
   */
  def argumentSorts(fun : IFunction,
                    arguments : Seq[Term]) : Seq[Sort] =
    functionType(fun, arguments)._1

  /**
   * Determine the argument types of any function.
   */
  def iArgumentSorts(fun : IFunction,
                     arguments : Seq[ITerm]) : Seq[Sort] =
    iFunctionType(fun, arguments)._1

  /**
   * Determine the sort of function results.
   */
  def resultSort(fun : IFunction,
                 arguments : Seq[Term]) : Sort =
    functionType(fun, arguments)._2

  /**
   * Determine the sort of function results.
   */
  def iResultSort(fun : IFunction,
                  arguments : Seq[ITerm]) : Sort =
    iFunctionType(fun, arguments)._2

}

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

////////////////////////////////////////////////////////////////////////////////

object MonoSortedIFunction {
  private val AC = Debug.AC_TYPES

  def apply(name : String,
            argSorts : Seq[Sort],
            resSort : Sort,
            partial : Boolean,
            relational : Boolean) : IFunction =
    if ((argSorts forall (_ == Sort.Integer)) && resSort == Sort.Integer)
      new IFunction(name, argSorts.size, partial, relational)
    else
      new MonoSortedIFunction(name, argSorts, resSort, partial, relational)

  /**
   * Determine the argument and result sorts of a
   * <code>MonoSortedIfunction</code>.
   */
  def functionType(f : IFunction) : (Seq[Sort], Sort) = f match {
    case f : MonoSortedIFunction =>
      (f.argSorts, f.resSort)
    case _ =>
      (for (_ <- 0 until f.arity) yield Sort.Integer, Sort.Integer)
  }
}

/**
 * Class for monomorphically sorted functions.
 */
class MonoSortedIFunction(_name : String,
                          val argSorts : Seq[Sort],
                          val resSort : Sort,
                          _partial : Boolean, _relational : Boolean)
      extends SortedIFunction(_name, argSorts.size, _partial, _relational) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(MonoSortedIFunction.AC,
                   (argSorts ++ List(resSort)) exists (_ != Sort.Integer))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

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

object SortedPredicate {
  /**
   * Determine the argument types of any predicate.
   */
  def argumentSorts(a : Atom) : Seq[Sort] = argumentSorts(a.pred, a)

  /**
   * Determine the argument types of any predicate.
   */
  def argumentSorts(pred : Predicate,
                    arguments : Seq[Term]) : Seq[Sort] = pred match {
    case pred : SortedPredicate =>
      pred argumentSorts arguments
    case _ =>
      for (_ <- 0 until pred.arity) yield Sort.Integer
  }

  /**
   * Determine the argument types of any predicate.
   */
  def iArgumentSorts(pred : Predicate,
                     arguments : Seq[ITerm]) : Seq[Sort] = pred match {
    case pred : SortedPredicate =>
      pred iArgumentSorts arguments
    case _ =>
      for (_ <- 0 until pred.arity) yield Sort.Integer
  }
}

/**
 * General class representing sorted predicates; sub-classes can model
 * both monomorphic and polymorphic predicates.
 */
abstract class SortedPredicate(_name : String, _arity : Int)
         extends Predicate(_name, _arity) {

  /**
   * Determine the argument types of the predicate.
   */
  def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort]

  /**
   * Determine the argument types of the predicate.
   */
  def argumentSorts(arguments : Seq[Term]) : Seq[Sort]

  /**
   * Given argument terms of the predicate, determine constraints on the
   * range of the arguments that are implied by the predicate. E.g., for a
   * predicate encoding a function, such constraints would be derived from
   * the sort of the result sort.
   */
  def sortConstraints(arguments : Seq[Term])
                     (implicit order : TermOrder) : Formula

}

////////////////////////////////////////////////////////////////////////////////

object MonoSortedPredicate {
  private val AC = Debug.AC_TYPES

  def apply(name : String, argSorts : Seq[Sort]) : Predicate =
    if (argSorts forall (_ == Sort.Integer))
      new Predicate(name, argSorts.size)
    else
      new MonoSortedPredicate(name, argSorts)

  /**
   * Determine the argument sorts of a <code>MonoSortedPredicate</code>.
   */
  def argumentSorts(pred : Predicate) : Seq[Sort] = pred match {
    case pred : MonoSortedPredicate => pred.argSorts
    case _ => for (_ <- 0 until pred.arity) yield Sort.Integer
  }
}

/**
 * Class for monomorphically sorted predicates
 */
class MonoSortedPredicate(_name : String, val argSorts : Seq[Sort])
         extends SortedPredicate(_name, argSorts.size) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(MonoSortedPredicate.AC,
                   argSorts exists (_ != Sort.Integer))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * Determine the argument types of the predicate.
   */
  def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = argSorts

  /**
   * Determine the argument types of the predicate.
   */
  def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = argSorts

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
