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

package ap.theories.bitvectors

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.{GroebnerMultiplication => Mul}
import ap.algebra.{Ring, PseudoRing, RingWithOrder, EuclidianRing,
                   CommutativeRing, RingWithIntConversions, Field}
import ap.util.Debug

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
      extends Ring with RingWithOrder
                   with CommutativeRing
                   with RingWithIntConversions {

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

  def isInt(s: ITerm): IFormula = true
  def ring2int(s: ITerm): ITerm = s

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

/**
 * Galois fields of cardinality <code>p</code>, for some prime
 * number <code>p</code>.
 */
case class GaloisField(p : IdealInt)
           extends ModRing(IdealInt.ZERO, p - 1) with Field {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Debug.AC_ALGEBRA, p isProbablePrime 3) // certainty level?
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  import IExpression._

  def div(s : ITerm, t : ITerm) : ITerm =
    // r = s / t <=>
    // r * t = s
    dom.eps(mul(v(0), VariableShiftVisitor(t, 0, 1)) ===
              VariableShiftVisitor(s, 0, 1))

}
