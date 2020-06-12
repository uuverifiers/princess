/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.algebra

import ap.basetypes.IdealInt
import ap.parser._
import ap.types.Sort
import ap.util.Debug

/**
 * A Pseudo-ring is a structure with the same operations as a ring, but
 * no guarantee that multiplication satisfies the ring axioms
 */
trait PseudoRing {

  /**
   * Domain of the ring
   */
  val dom : Sort

  /**
   * Conversion of an integer term to a ring term
   */
  def int2ring(s : ITerm) : ITerm

  /**
   * The zero element of this ring
   */
  def zero : ITerm

  /**
   * The one element of this ring
   */
  def one : ITerm

  /**
   * Ring addition
   */
  def plus(s : ITerm, t : ITerm) : ITerm

  /**
   * N-ary sums
   */
  def summation(terms : ITerm*) : ITerm = (zero /: terms)(plus)

  /**
   * Additive inverses
   */
  def minus(s : ITerm) : ITerm

  /**
   * Difference between two terms
   */
  def minus(s : ITerm, t : ITerm) : ITerm = plus(s, minus(t))

  /**
   * Ring multiplication
   */
  def mul(s : ITerm, t : ITerm) : ITerm

  /**
   * <code>num * s</code>
   */
  def times(num : IdealInt, s : ITerm) : ITerm = mul(int2ring(IIntLit(num)), s)

  /**
   * N-ary sums
   */
  def product(terms : ITerm*) : ITerm = (one /: terms)(mul)

  /**
   * Addition gives rise to an Abelian group
   */
  def additiveGroup : Group with Abelian = new Group with Abelian {
    val dom = PseudoRing.this.dom
    def zero = PseudoRing.this.zero
    def op(s : ITerm, t : ITerm) = plus(s, t)
    def minus(s : ITerm) = PseudoRing.this.minus(s)

    override def times(num : IdealInt, s : ITerm) : ITerm =
      PseudoRing.this.times(num, s)
  }

}

/**
 * Rings are structures with both addition and multiplication
 */
trait Ring extends PseudoRing {

  /**
   * Multiplication gives rise to a monoid
   */
  def multiplicativeMonoid : Monoid = new Monoid {
    val dom = Ring.this.dom
    def zero = Ring.this.one
    def op(s : ITerm, t : ITerm) = mul(s, t)
  }

}

trait CommutativePseudoRing extends PseudoRing

trait CommutativeRing extends Ring with CommutativePseudoRing {

  /**
   * Multiplication gives rise to an Abelian monoid
   */
  override def multiplicativeMonoid : Monoid with Abelian =
    new Monoid with Abelian {
      val dom = CommutativeRing.this.dom
      def zero = CommutativeRing.this.one
      def op(s : ITerm, t : ITerm) = mul(s, t)
    }

}

/**
 * Rings that also have a division operation (though possibly not
 * satisfying the standard axioms)
 */
trait RingWithDivision extends PseudoRing {

  /**
   * Division operation
   */
  def div(s : ITerm, t : ITerm) : ITerm

}

/**
 * Euclidian rings extend rings with operations for division and
 * remainder, with the Euclidian definition:
 * <code>plus(mul(div(s, t), t), mod(s, t)) === s</code>,
 * with <code>f(mod(s, t)) in [0, abs(t))</code> for some appropriate
 * embedding into real numbers.
 */
trait EuclidianRing extends Ring with RingWithDivision {

  /**
   * Euclidian division
   */
  def div(s : ITerm, t : ITerm) : ITerm

  /**
   * Euclidian remainder
   */
  def mod(s : ITerm, t : ITerm) : ITerm

}

/**
 * Rings that also possess an ordering relation
 */
trait RingWithOrder extends PseudoRing {

  /**
   * Less-than operator
   */
  def lt(s : ITerm, t : ITerm) : IFormula

  /**
   * Less-than-or-equal operator
   */
  def leq(s : ITerm, t : ITerm) : IFormula

  /**
   * Greater-than operator
   */
  def gt(s : ITerm, t : ITerm) : IFormula = lt(t, s)

  /**
   * Greater-than-or-equal operator
   */
  def geq(s : ITerm, t : ITerm) : IFormula = leq(t, s)

}

/**
 * Ordered rings are rings with ordering relation in which
 * addition, multiplication, and ordering are consistent:
 * <code>leq(s, t) ==> leq(plus(s, a), plus(t, a))</code> and
 * <code>leq(zero, s) & leq(zero, t) ==> leq(zero, mul(s, t))</code>.
 */
trait OrderedRing extends Ring with RingWithOrder

/**
 * Fields are commutative rings in which all non-zero elements have
 * multiplicative inverses.
 */
trait Field extends CommutativeRing with RingWithDivision {

  def inverse(s : ITerm) : ITerm = div(one, s)

  /**
   * Non-zero elements now give rise to an Abelian group
   */
  def multiplicativeGroup : Group with Abelian =
    new Group with Abelian {
      val dom = Field.this.dom // TODO: how to remove the zero?
      def zero = Field.this.one
      def op(s : ITerm, t : ITerm) = mul(s, t)
      def minus(s : ITerm) : ITerm = inverse(s)
    }

}
