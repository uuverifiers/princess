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

package ap.theories.bitvectors

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.{GroebnerMultiplication => Mul}
import ap.theories.algebra.{PseudoRing, RingWithOrder, EuclidianRing}

/**
 * Modular arithmetic in the interval <code>[lower, upper]</code>.
 */
object ModRing {

  def apply(lower : IdealInt, upper : IdealInt) =
    new ModRing(lower, upper)

  def unapply(r : PseudoRing) : Option[(IdealInt, IdealInt)] = r match {
    case r : ModRing => Some((r.lower, r.upper))
    case _           => None
  }

}

/**
 * Modular arithmetic in the interval <code>[lower, upper]</code>.
 */
class ModRing(val lower : IdealInt, val upper : IdealInt)
      extends RingWithOrder {

  import ModuloArithmetic.{cast2Interval, ModSort}

  val dom = ModSort(lower, upper)
  def int2ring(s : ITerm) = cast2Interval(lower, upper, s)

  val zero: ITerm = int2ring(IIntLit(0))
  val one: ITerm  = int2ring(IIntLit(1))

  def plus(s: ITerm, t: ITerm): ITerm = int2ring(s + t)
  def mul (s: ITerm, t: ITerm): ITerm = int2ring(Mul.mult(s, t))

  def minus(s: ITerm): ITerm = int2ring(-s)

  def lt (s : ITerm, t : ITerm) : IFormula = (s < t)
  def leq(s : ITerm, t : ITerm) : IFormula = (s <= t)

}

/**
 * Ring of unsigned fixed-size bit-vectors
 */
case class UnsignedBVRing(bits : Int)
           extends ModRing(IdealInt.ZERO,
                           ModuloArithmetic.pow2MinusOne(bits))
           with    EuclidianRing {

  import ModuloArithmetic.{bvudiv, bvurem}

  def div(s : ITerm, t : ITerm) : ITerm = bvudiv(s, t)
  def mod(s : ITerm, t : ITerm) : ITerm = bvurem(s, t)

}

/**
 * Ring of signed fixed-size bit-vectors
 */
case class SignedBVRing(bits : Int)
           extends ModRing(-ModuloArithmetic.pow2(bits - 1),
                           ModuloArithmetic.pow2MinusOne(bits - 1))
           with    EuclidianRing {

  import ModuloArithmetic.{bvsdiv, bvsrem}

  def div(s : ITerm, t : ITerm) : ITerm = bvsdiv(s, t)
  def mod(s : ITerm, t : ITerm) : ITerm = bvsrem(s, t)

}
