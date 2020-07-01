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

  def lt(s : ITerm, t : ITerm) : IFormula = s < t

  def leq(s : ITerm, t : ITerm) : IFormula = s <= t

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

}

