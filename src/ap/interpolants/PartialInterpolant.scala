/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.interpolants

import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.TermOrder
import ap.proof.certificates.{CertArithLiteral, CertEquation,
                              CertNegEquation, CertInequality}
import ap.basetypes.IdealInt
import ap.util.Debug


object PartialInterpolant {
  
  private val AC = Debug.AC_INTERPOLATION
  
  object Kind extends Enumeration {
    val EqLeft, InEqLeft, EqRight, NegEqRight = Value
  }

  def eqLeft(linComb : LinearCombination) : PartialInterpolant =
    apply(linComb, Kind.EqLeft)

  def inEqLeft(linComb : LinearCombination) : PartialInterpolant =
    apply(linComb, Kind.InEqLeft)

  def eqRight(linComb : LinearCombination) : PartialInterpolant =
    apply(linComb, Kind.EqRight)

  def negEqRight(linComb : LinearCombination) : PartialInterpolant =
    apply(linComb, Kind.NegEqRight)

  def apply(linComb : LinearCombination,
            kind : PartialInterpolant.Kind.Value) : PartialInterpolant =
    apply(linComb, IdealInt.ONE, kind)

  def apply(linComb : LinearCombination,
            den : IdealInt,
            kind : PartialInterpolant.Kind.Value) : PartialInterpolant = {
    val commonFactor = linComb.nonConstCoeffGcd gcd linComb.constant gcd den
    new PartialInterpolant(linComb / commonFactor, den / commonFactor, kind)
  }
  
  def sum(terms : Seq[(IdealInt, PartialInterpolant)], kind : Kind.Value)
         (implicit order : TermOrder) : PartialInterpolant = {
    val denLCM = IdealInt lcm (for ((_, pi) <- terms.iterator) yield pi.den)
    
    val newLinComb = LinearCombination.sum(for ((c, pi) <- terms.iterator)
                                             yield (c * denLCM / pi.den, pi.linComb),
                                           order)
    
    apply(newLinComb, denLCM, kind)
  }

}

/**
 * Class representing the different kinds of partial interpolants that are
 * used to annotate arithmetic literals. A partial interpolant carries a
 * "denominator", which represents a factor that the annotated arithmetic
 * literal has to be multiplied with to make the partial interpolant valid. E.g.
 * <code>x = 0 [y = 0, 2]</code> can be interpreted as equivalent to
 * <code>2*x = 0 [y = 0, 1]</code>.
 */
class PartialInterpolant private (val linComb : LinearCombination,
                                  val den : IdealInt,
                                  val kind : PartialInterpolant.Kind.Value) {
  
  import PartialInterpolant.Kind._
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PartialInterpolant.AC,
                   (linComb.nonConstCoeffGcd gcd linComb.constant gcd den).isOne &&
                   den.signum > 0)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def compatible(literal : CertArithLiteral) : Boolean = (literal, kind) match {
    case (_ : CertEquation, EqLeft) |
         (_ : CertNegEquation, EqRight | NegEqRight) |
         (_ : CertInequality, InEqLeft) => true
    case _ => false
  }
  
  def toConjunction : ArithConj = {
    implicit val o = linComb.order
    kind match {
      case EqLeft | NegEqRight => EquationConj(linComb, o)
      case InEqLeft =>            InEqConj(linComb, o)
      case EqRight =>             NegEquationConj(linComb, o)
    }
  }
  
  def /(factor : IdealInt) : PartialInterpolant =
    if (factor.isOne)
      this
    else if (factor.signum < 0)
      PartialInterpolant(-linComb, den * (-factor), kind)
    else
      PartialInterpolant(linComb, den * factor, kind)

  override def toString : String =
    "[" + linComb + (kind match { case EqLeft | EqRight => " = 0"
                                  case NegEqRight => " != 0"
                                  case InEqLeft => " >= 0" }) +
    ", " + den + "]"
  
}
 
