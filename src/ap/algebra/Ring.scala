/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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
  def summation(terms : ITerm*) : ITerm =
    if (terms.isEmpty)
      zero
    else
      terms reduceLeft (plus _)

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
  def product(terms : ITerm*) : ITerm =
    if (terms.isEmpty)
      one
    else
      terms reduceLeft (mul _)

  /**
   * Addition gives rise to an Abelian group
   */
  def additiveGroup : Group with Abelian with SymbolicTimes =
    new Group with Abelian with SymbolicTimes {
      val dom                      = PseudoRing.this.dom
      def identity                 = PseudoRing.this.zero
      def op(s : ITerm, t : ITerm) = PseudoRing.this.plus(s, t)
      def inverse(s : ITerm)       = PseudoRing.this.minus(s)

      override def times(num : IdealInt, s : ITerm) : ITerm =
        PseudoRing.this.times(num, s)
      def times(num : ITerm, s : ITerm) : ITerm =
        mul(int2ring(num), s)
    }

  override def toString = dom.toString

}

/**
 * Rings are structures with both addition and multiplication
 */
trait Ring extends PseudoRing {

  /**
   * Multiplication gives rise to a monoid
   */
  def multiplicativeMonoid : Monoid = new Monoid {
    val dom                      = Ring.this.dom
    def identity                 = Ring.this.one
    def op(s : ITerm, t : ITerm) = Ring.this.mul(s, t)
  }

}

trait CommutativePseudoRing extends PseudoRing

trait CommutativeRing extends Ring with CommutativePseudoRing {

  /**
   * Multiplication gives rise to an Abelian monoid
   */
  override def multiplicativeMonoid : Monoid with Abelian =
    new Monoid with Abelian {
      val dom                      = CommutativeRing.this.dom
      def identity                 = CommutativeRing.this.one
      def op(s : ITerm, t : ITerm) = CommutativeRing.this.mul(s, t)
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
trait EuclidianRing extends CommutativeRing with RingWithDivision {

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
 * Ring that can also convert ring elements back to integers.
 */
trait RingWithIntConversions extends PseudoRing {

  /**
   * Conversion of a ring term to an integer term.
   * This should have the property that
   *  <code>isInt(s) <=> int2Ring(ring2Int(s)) === s</code>.
   */
  def ring2int(s : ITerm) : ITerm

  /**
   * Test whether a ring element represents an integer number.
   */
  def isInt(s : ITerm) : IFormula

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
      // TODO: how to remove the zero in the best way?
      val dom                        = Field.this.dom
      def identity                   = Field.this.one
      def op(s : ITerm, t : ITerm)   = mul(s, t)
      def inverse(s : ITerm) : ITerm = Field.this.inverse(s)
    }

}
