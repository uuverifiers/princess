/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.rationals

import ap.parser._
import ap.theories._
import ap.basetypes.IdealInt
import ap.algebra.{Ring, RingWithDivision, IntegerRing, Field, OrderedRing,
                   RingWithIntConversions}

/**
 * The theory and field of rational numbers.
 */
object Rationals extends Fractions("Rat", IntegerRing, IExpression.v(0) > 0)
                 with Field with OrderedRing with RingWithIntConversions {

  import IExpression._

  override val dependencies = List(GroebnerMultiplication)

  protected override
    def simplifyFraction(n : ITerm, d : ITerm) : (ITerm, ITerm) = (n, d) match {
      case (IIntLit(n), IIntLit(d)) => {
        val l = n gcd d
        (IIntLit(n / l), IIntLit(d / l))
      }
      case _ =>
        (n, d)
    }

  protected override def individualsStream : Option[Stream[ITerm]] = Some({
    val numStream =
      Stream.iterate(IdealInt.ZERO){ n => if (n.signum <= 0) (-n+1) else -n }
    val denomStream =
      Stream.iterate(IdealInt.ONE) { n => n + 1 }

    for (n  <- Stream.iterate(0)(n => n + 1);
         nthNum   = numStream(n);
         nthDenom = denomStream(n);
         (num, den) <- (for (t <- denomStream take n)   yield (nthNum, t)) ++
                       (for (t <- numStream take (n+1)) yield (t, nthDenom));
         if (num gcd den) == IdealInt.ONE)
    yield (frac(i(num), i(den)))
  })

  def lt(s : ITerm, t : ITerm) : IFormula = (s, t) match {
    case (IFunApp(`int`, Seq(s)), IFunApp(`int`, Seq(t))) =>
      s < t
    case (IFunApp(`int`, Seq(Const(IdealInt.ZERO))), t) =>
      0 < t
    case (s, IFunApp(`int`, Seq(Const(IdealInt.ZERO)))) =>
      s < 0
    case (s, t) =>
      s < t
  }

  def leq(s : ITerm, t : ITerm) : IFormula = (s, t) match {
    case (IFunApp(`int`, Seq(s)), IFunApp(`int`, Seq(t))) =>
      s <= t
    case (IFunApp(`int`, Seq(Const(IdealInt.ZERO))), t) =>
      0 <= t
    case (s, IFunApp(`int`, Seq(Const(IdealInt.ZERO)))) =>
      s <= 0
    case (s, t) =>
      s <= t
  }

  /**
   * Conversion of a rational term to an integer term, the
   * floor operator.
   */
  def ring2int(s : ITerm) : ITerm =
    eps(ex(v(1) === GroebnerMultiplication.eDiv(
                      VariableShiftVisitor(s, 0, 2), v(0)) &
           v(0) === denom() &
           v(0) > 0))

  /**
   * Test whether a rational is integer.
   */
  def isInt(s : ITerm) : IFormula =
    eqZero(eps(ex(v(1) === GroebnerMultiplication.eMod(
                             VariableShiftVisitor(s, 0, 2), v(0)) &
                  v(0) === denom() &
                  v(0) > 0)))

  val RatDivZeroTheory =
    new DivZero("RatDivZero",
                List(("ratDivZero", Rationals.dom)))

  /**
   * Uninterpreted function representing the SMT-LIB rational division
   * by zero.
   */
  val RatDivZero = RatDivZeroTheory.functions(0)

  /**
   * Division, assuming SMT-LIB semantics for division by zero.
   */
  def divWithSpecialZero(s : ITerm, t : ITerm) : ITerm =
    DivZero.handleZero(div _, RatDivZero, zero, dom)(s, t)
}

