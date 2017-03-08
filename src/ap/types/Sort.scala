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

import ap.basetypes.IdealInt
import ap.parser._
import ap.terfor.{Term, Formula, TermOrder, OneTerm, ConstantTerm}
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.util.Debug

object Sort {

  private val AC = Debug.AC_TYPES

  /**
   * The sort of integers, which is also the default sort whenever
   * no sort is specified.
   */
  object Integer extends Sort {
    val name : String = "Int"
    def membershipConstraint(t : ITerm) : IFormula =
      IExpression.i(true)
    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
      Conjunction.TRUE
    val cardinality : Option[IdealInt] = None
    override def newConstant(name : String) : ConstantTerm =
      new ConstantTerm(name)
  }

  /**
   * The sort of natural numbers.
   */
  object Nat extends ProxySort(Interval(Some(IdealInt.ZERO), None)) {
    override val name : String = "Nat"
  }

  /**
   * Sort representing (possibly left- or right-open) intervals.
   */
  case class Interval(lower : Option[IdealInt], upper : Option[IdealInt])
             extends Sort {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC,
                     (lower, upper) match {
                       case (Some(l), Some(u)) => l <= u
                       case _ => true
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val name : String =
      (lower match { case Some(l) => "[" + l
                     case None    => "(-infty" }) + ", " +
      (upper match { case Some(u) => "" + u + "]"
                     case None    => "infty)" })

    def membershipConstraint(t : ITerm) : IFormula = {
      import IExpression._
      (lower match { case Some(l) => t >= l
                     case None    => i(true) }) &&&
      (upper match { case Some(u) => t <= u
                     case None    => i(true) })
    }

    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula = {
      val lcs =
        (lower match { case Some(l) => List(LinearCombination(
                                              Array((IdealInt.ONE, t),
                                                    (-l, OneTerm)), order))
                       case None    => List() }) ++
        (upper match { case Some(u) => List(LinearCombination(
                                              Array((IdealInt.MINUS_ONE, t),
                                                    (u, OneTerm)), order))
                       case None    => List() })
      InEqConj(lcs, order)
    }

    val cardinality =
      for (l <- lower; u <- upper) yield (u - l + 1)

  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Trait representing sorts of individuals in the logic.
 */
trait Sort {
  val name : String

  def membershipConstraint(t : ITerm) : IFormula

  def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula

  val cardinality : Option[IdealInt]

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = name

  def newConstant(name : String) : ConstantTerm =
    new SortedConstantTerm(name, this)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def ex(f : IFormula) =
    IQuantified(Quantifier.EX,
                IExpression.guardEx(f, membershipConstraint(IVariable(0))))
  
  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def all(f : IFormula) =
    IQuantified(Quantifier.ALL,
                IExpression.guardAll(f, membershipConstraint(IVariable(0))))

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.ex(a => phi(a))</code>.
   */
  def ex(f : ITerm => IFormula) =
    IExpression.ex(x => IExpression.guardEx(f(x), membershipConstraint(x)))

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.all(a => phi(a))</code>.
   */
  def all(f : ITerm => IFormula) =
    IExpression.all(x => IExpression.guardAll(f(x), membershipConstraint(x)))

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to define proxy sorts, which inherit most properties from some
 * underlying sort, but may override some of the features.
 */
class ProxySort(underlying : Sort) extends Sort {
  val name : String = underlying.name

  def membershipConstraint(t : ITerm) : IFormula =
    underlying.membershipConstraint(t)

  def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
    underlying.membershipConstraint(t)

  val cardinality : Option[IdealInt] = underlying.cardinality
}