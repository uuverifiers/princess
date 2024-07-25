/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, Formula}
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
  
  def toFormula : Formula =
    kind match {
      case EqLeft | NegEqRight => EquationConj(linComb, linComb.order)
      case InEqLeft =>            InEqConj(linComb, linComb.order)
      case EqRight =>             NegEquationConj(linComb, linComb.order)
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
 
