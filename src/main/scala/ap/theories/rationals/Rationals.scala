/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.Signature
import ap.parser._
import ap.theories._
import ap.basetypes.IdealInt
import ap.algebra.{Ring, RingWithDivision, IntegerRing, Field, OrderedRing,
                   RingWithIntConversions}

/**
 * The theory and field of rational numbers.
 */
object Rationals
  extends OrderedFractions("Rat", IntegerRing, IExpression.v(0) > 0)
  with Field with RingWithIntConversions {

  import IExpression._
  import IntegerRing.{int2ring => ringInt2Ring}

  private val ignoreQuantifiersFlag =
    new scala.util.DynamicVariable[Array[Boolean]] (Array(false))

  ignoreQuantifiersFlag.value = Array(false)

  private def ignoreQuantifiers : Boolean = ignoreQuantifiersFlag.value(0)

  private val ringOne      = IntegerRing.one
  private val ringMinusOne = ringInt2Ring(-1)

  /**
   * Hack to enable other theories to use rationals even in axioms with
   * quantifiers. This should be removed as soon as the incompatibility of
   * rationals and quantifiers has been resolved.
   */
  protected[ap] def ignoringQuantifiers[A](comp : => A) : A =
    ignoreQuantifiersFlag.withValue(Array(true)) { comp }

  override val dependencies = List(GroebnerMultiplication)

  override def iPreprocess(f : IFormula, signature : Signature)
                        : (IFormula, Signature) = {
    val (res, newSig) = fracPreproc(f, signature)
    if (!ignoreQuantifiers)
      IncompletenessChecker.visitWithoutResult(res, Context(()))
    (res, newSig)
  }

  protected override
    def simplifyFraction(n : ITerm, d : ITerm) : (ITerm, ITerm) = (n, d) match {
      case (Const(n), Const(d)) => {
        val l = n gcd d
        if (d.signum < 0)
          (IIntLit(-n / l), IIntLit(-d / l))
        else
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


  /////////////////////////////////////////////////////////////////////////////

  private object BackTranslator extends CollectingVisitor[Unit, IExpression] {
    def postVisit(expr : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      (expr, subres) match {
        case (_ : IEquation, Seq(t1 : ITerm, t2 : ITerm))
            if termNeedsRewr(t1) || termNeedsRewr(t2) => {
          val (s1, r1) = divByDenom(t1)
          val (s2, r2) = divByDenom(t2)
          if (r1 == r2)
            s1 === s2
          else
            false
        }
        case (IIntFormula(IIntRelation.EqZero, _), Seq(t : ITerm))
            if termNeedsRewr(t) => {
          val (s, r) = divByDenom(t)
          if (r.isZero)
            s === zero
          else
            false
        }
        case (IIntFormula(IIntRelation.GeqZero, _), Seq(t : ITerm))
            if termNeedsRewr(t) => {
          val (s, r) = divByDenom(t)
          r.signum match {
            case -1 => lessThan(zero, s)
            case 0  => lessThanOrEqual(zero, s)
            case 1  => throw new Exception(
                         "cannot back-translate rational inequality " +
                         (expr update subres))
          }
        }

        case _ => expr update subres
      }
  }

  override def iPostprocess(f : IFormula, signature : Signature) : IFormula =
    BackTranslator.visit(f, ()).asInstanceOf[IFormula]

  /////////////////////////////////////////////////////////////////////////////

  private def simplifyRationals(e : IExpression) : IExpression = e match {
    case e => e
  }

  override protected def simplifiers =
    super.simplifiers ++ List(simplifyRationals _)

  /////////////////////////////////////////////////////////////////////////////

      import IExpression.Sort.:::

  val Var0Eq = SymbolEquation(v(0, dom))

  private def postSimplifyAtoms(e : IExpression) : IExpression = e match {
    case Eq(ISortedVariable(0, `dom`), t) if !ContainsVariable(t, 0) =>
      e

    case Var0Eq(Const(num), Const(denom), remainder)
      if !num.isZero && !denom.isZero =>
      v(0, dom) === multWithFraction(denom, num, remainder)

    case Eq(`denomT`, ITimes(coeff, t))
      if !coeff.isZero && !termNeedsRewr(t) => {
      t === Fraction(ringOne, coeff)
    }
    case Eq(ITimes(coeff1, `denomT`), ITimes(coeff2, t))
      if !coeff2.isZero && !termNeedsRewr(t) => {
      t === Fraction(coeff1, coeff2)
    }
    case Eq(ITimes(coeff2, t), ITimes(coeff1, `denomT`))
      if !coeff2.isZero && !termNeedsRewr(t) => {
      t === Fraction(coeff1, coeff2)
    }

    /*
    case Eq(IFunApp(`multWithRing`, Seq(coeff, s : IVariable)), t)
      if !t.isInstanceOf[IVariable] && isNonZeroRingTerm(coeff) =>
      s === multWithFraction(ringOne, coeff, t)
    case Eq(t, IFunApp(`multWithRing`, Seq(coeff, s : IVariable)))
      if !t.isInstanceOf[IVariable] && isNonZeroRingTerm(coeff) =>
      s === multWithFraction(ringOne, coeff, t)
*/

    case t => t
  }

  protected def termNeedsRewr(t : ITerm) : Boolean = {
    import IExpression.Sort.:::
    t match {
      case IPlus(_ ::: `dom`, _)  => true
      case IPlus(_, _ ::: `dom`)  => true
      case ITimes(_, _ ::: `dom`) => true
      case IPlus(s, t)            => termNeedsRewr(s) || termNeedsRewr(t)
      case ITimes(_, s)           => termNeedsRewr(s)
      case `denomT`               => true
      case _                      => false
    }
  }

  /**
   * Divide each term of a sum by the <code>denom()</code> term, rewriting
   * accordingly. Constant terms are dropped and their sum is returned
   * as the second result.
   */
  def divByDenom(t : ITerm) : (ITerm, IdealInt) = {
    t match {
      // TODO: add multiplication
      case IPlus(t1, t2) => {
        val (s1, r1) = divByDenom(t1)
        val (s2, r2) = divByDenom(t2)
        (addition(s1, s2), r1 + r2)
      }
      case ITimes(coeff, t1) => {
        val (s1, r1) = divByDenom(t1)
        (multWithRing(ringInt2Ring(coeff), s1), coeff * r1)
      }
      case `denomT` =>
        (one, 0)
      case IIntLit(value) =>
        (zero, value)
      case IVariable(n) =>
        (v(n, dom), 0)
      case t =>
        (t, 0)
    }
  }

  override def postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ simplifiers ++ List(postSimplifyAtoms _)

  /////////////////////////////////////////////////////////////////////////////

  val RatDivZeroTheory =
    new DivZero("RatDivZero",
                List(("ratDivZero", Rationals.dom)))

  protected override def isNonZeroRingTerm(t : ITerm) : Boolean =
    t match {
      case Const(n) if !n.isZero => true
      case _                     => false
    }

  /**
   * Uninterpreted function representing the SMT-LIB rational division
   * by zero.
   */
  val RatDivZero = RatDivZeroTheory.functions(0)

  /**
   * Division, assuming SMT-LIB semantics for division by zero.
   */
  def divWithSpecialZero(s : ITerm, t : ITerm) : ITerm =
    DivZero.handleZero(div _, RatDivZero, zero,
                       { case `zero` => true; case _ => false },
                       { case IFunApp(`fromRing`, Seq(Const(n)))
                              if !n.isZero => true
                         case _ => false },
                       dom)(s, t)
}

