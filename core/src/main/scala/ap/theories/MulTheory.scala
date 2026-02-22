/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.parameters.Param

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}

object MulTheory {

  /**
   * Extractor recognising the <code>mul</code> function of
   * any multiplication theory.
   */
  object Mul {
    def unapply(fun : IFunction) : Boolean =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : MulTheory) => fun == t.mul
        case _ => false
      }
  }

}

/**
 * Trait for theories providing general, non-linear multiplication.
 */
trait MulTheory extends Theory {

  /**
   * Symbol representing proper (non-linear) multiplication
   */
  val mul : IFunction

  /**
   * Multiply two terms, using the <code>mul</code> function if necessary;
   * if any of the two terms is constant, normal Presburger
   * multiplication will be used.
   */
  def mult(t1 : ITerm, t2 : ITerm) : ITerm =
    try {
      t1 * t2
    } catch {
      case _ : IllegalArgumentException => IFunApp(mul, List(t1, t2))
    }

  import IExpression._

  /**
   * Multiply two terms, using the <code>mul</code> function if necessary;
   * if any of the two terms is constant, normal Presburger
   * multiplication will be used, and simple terms will directly be simplified.
   */
  def multSimplify(t1 : ITerm, t2 : ITerm) : ITerm =
    (t1, t2) match {
      case (Const(t1), t2) => t2 *** t1
      case (t1, Const(t2)) => t1 *** t2
      case (t1, t2)        => IFunApp(mul, List(t1, t2))
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Euclidian division
   */
  def eDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    (numTerm, denomTerm) match {
      case (_, Const(IdealInt.ZERO)) =>
        // This is an undefined case, translate as a partial function
        eps(false)
      case (Const(num), Const(denom)) =>
        num / denom
      case (SimpleTerm(numTerm), Const(denom)) => {
        val num = VariableShiftVisitor(numTerm, 0, 1)
        val v0Denom = mult(v(0), denom)
        denom match {
          case IdealInt(2 | -2) =>
            // for the special case of denominator two, it is usually
            // more efficient to split
            eps((num === v0Denom) | (num === v0Denom + 1))
          case _ =>
            eps((v0Denom <= num) & (v0Denom > num - denom.abs))
        }
      }
      case _ => {
        // avoid duplication of the numerator by introducing a quantifier

        val num = VariableShiftVisitor(numTerm, 0, 4)
        val denom = VariableShiftVisitor(denomTerm, 0, 4)

        eps(ex(ex(ex((v(0) === num) &
                     (v(1) === mult(v(3), v(2))) &
                     (v(2) === denom) &
                     (denomTerm match {
                        case Const(IdealInt(2 | -2)) =>
                          // for the special case of denominator two, it
                          // is usually more efficient to split
                          (v(0) === v(1)) | (v(0) === v(1) + 1)
                        case _ =>
                          (v(1) <= v(0)) & (v(1) > v(0) - abs(v(2)))
                      })))))
      }
    }

  /**
   * Euclidian division, assuming the SMT-LIB semantics for division
   * by zero.
   */
  def eDivWithSpecialZero(num : ITerm, denom : ITerm) : ITerm =
    DivZero.handleIntZero(eDiv _, DivZero.IntDivZero, Sort.Integer)(num, denom)

  /**
   * Euclidian remainder
   */
  def eMod(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    (numTerm, denomTerm) match {
      case (_, Const(IdealInt.ZERO)) =>
        // This is an undefined case, translate as a partial function
        eps(false)
      case (Const(num), Const(denom)) =>
        num % denom
      case _ => {
        val num = VariableShiftVisitor(numTerm, 0, 1)
        val denom = VariableShiftVisitor(denomTerm, 0, 1)

        eps((v(0) >= 0) & (v(0) < abs(denom)) &
              ex(VariableShiftVisitor(num, 0, 1) ===
                   mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
      }
    }

  /**
   * Euclidian remaining, assuming the SMT-LIB semantics for remainder
   * by zero.
   */
  def eModWithSpecialZero(num : ITerm, denom : ITerm) : ITerm =
    DivZero.handleIntZero(eMod _, DivZero.IntModZero, Sort.Integer)(num, denom)

  /**
   * Truncation division
   */
  def tDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm) && Const.unapply(denomTerm).isDefined) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      val rem = num - mult(v(0), denom)
      eps((rem < abs(denom)) & (-rem < abs(denom)) &
          ((rem > 0) ==> (num > 0)) & ((rem < 0) ==> (num < 0)))
    } else {
      // avoid duplication of terms by introducing quantifiers

      val num = VariableShiftVisitor(numTerm, 0, 4)
      val denom = VariableShiftVisitor(denomTerm, 0, 4)

      eps(ex(ex(ex((v(0) === num) &
                   (v(1) === v(0) - mult(v(3), v(2))) &
                   (v(2) === denom) &
                   (v(1) < abs(v(2))) & (-v(1) < abs(v(2))) &
                   ((v(1) > 0) ==> (v(0) > 0)) & ((v(1) < 0) ==> (v(0) < 0))))))
    }

  /**
   * Truncation remainder
   */
  def tMod(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm)) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      eps((v(0) < abs(denom)) & (-v(0) < abs(denom)) &
          ((v(0) > 0) ==> (num > 0)) & ((v(0) < 0) ==> (num < 0)) &
          ex(VariableShiftVisitor(num, 0, 1) ===
             mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
    } else {
      // avoid duplication of the numerator by introducing a quantifier

      val num = VariableShiftVisitor(numTerm, 0, 2)
      val denom = VariableShiftVisitor(denomTerm, 0, 2)

      eps(ex((v(0) === num) &
             (v(1) < abs(denom)) & (-v(1) < abs(denom)) &
             ((v(1) > 0) ==> (v(0) > 0)) & ((v(1) < 0) ==> (v(0) < 0)) &
             ex(v(1) === mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(2))))
    }

  /**
   * Floor division
   */
  def fDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm)) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      val rem = num - mult(v(0), denom)
      eps((rem < abs(denom)) & (-rem < abs(denom)) &
          ((rem > 0) ==> (denom > 0)) & ((rem < 0) ==> (denom < 0)))
    } else {
      // avoid duplication of the numerator by introducing a quantifier

      val num = VariableShiftVisitor(numTerm, 0, 2)
      val denom = VariableShiftVisitor(denomTerm, 0, 2)

      val rem = v(0) - mult(v(1), denom)
      eps(ex((v(0) === num) &
             (rem < abs(denom)) & (-rem < abs(denom)) &
             ((rem > 0) ==> (denom > 0)) & ((rem < 0) ==> (denom < 0))))
    }

  /**
   * Floor remainder
   */
  def fMod(numTerm : ITerm, denomTerm : ITerm) : ITerm = {
    val num = VariableShiftVisitor(numTerm, 0, 1)
    val denom = VariableShiftVisitor(denomTerm, 0, 1)

    eps((v(0) < abs(denom)) & (-v(0) < abs(denom)) &
        ((v(0) > 0) ==> (denom > 0)) & ((v(0) < 0) ==> (denom < 0)) &
        ex(VariableShiftVisitor(num, 0, 1) ===
           mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
  }

  /**
   * Exponentiation, with non-negative exponent
   */
  def pow(basis : ITerm, expTerm : ITerm) : ITerm = expTerm match {
    case Const(exp) => exp.signum match {
      case -1 =>
        throw new IllegalArgumentException
      case 0 =>
        1
      case 1 =>
        (for (_ <- 0 until exp.intValueSafe) yield basis) reduceLeft (mult _)
    }
    case _ =>
      throw new IllegalArgumentException
  }

  //////////////////////////////////////////////////////////////////////////////

  class RichMulTerm(term : ITerm) {
    /**
     * Multiply two terms, using the <code>MulTheory.mul</code> function
     * if necessary;
     * if any of the two terms is constant, normal Presburger
     * multiplication will be used.
     */
    def **(that : ITerm) : ITerm  = mult(term, that)

    /**
     * Euclidian division
     */
    def /(that : ITerm) : ITerm  = MulTheory.this.eDiv(term, that)

    /**
     * Euclidian remainder
     */
    def %(that : ITerm) : ITerm  = MulTheory.this.eMod(term, that)

    /**
     * Euclidian division
     */
    def eDiv(that : ITerm) : ITerm = MulTheory.this.eDiv(term, that)

    /**
     * Euclidian division, assuming the SMT-LIB semantics for division
     * by zero.
     */
    def eDivWithSpecialZero(that : ITerm) : ITerm =
      MulTheory.this.eDivWithSpecialZero(term, that)

    /**
     * Euclidian remainder
     */
    def eMod(that : ITerm) : ITerm = MulTheory.this.eMod(term, that)

    /**
     * Euclidian remaining, assuming the SMT-LIB semantics for remainder
     * by zero.
     */
    def eModWithSpecialZero(that : ITerm) : ITerm =
      MulTheory.this.eModWithSpecialZero(term, that)

    /**
     * Truncation division
     */
    def tDiv(that : ITerm) : ITerm = MulTheory.this.tDiv(term, that)

    /**
     * Truncation remainder
     */
    def tMod(that : ITerm) : ITerm = MulTheory.this.tMod(term, that)

    /**
     * Floor division
     */
    def fDiv(that : ITerm) : ITerm = MulTheory.this.fDiv(term, that)

    /**
     * Floor remainder
     */
    def fMod(that : ITerm) : ITerm = MulTheory.this.fMod(term, that)

    /**
     * Exponentiation, with non-negative exponent. Note that <code>^</code>
     * binds only weakly in Scala, so usually one has to write <code>(x^2)</code>
     * with parentheses.
     */
    def ^(exp : ITerm) : ITerm = pow(term, exp)
  }

  implicit def convert2RichMulTerm(term : ITerm) : RichMulTerm =
    new RichMulTerm(term)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : IExpression) : IExpression =
    MulConverter.visit(expr, ())

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : ITerm) : ITerm =
    MulConverter.visit(expr, ()).asInstanceOf[ITerm]

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : IFormula) : IFormula =
    MulConverter.visit(expr, ()).asInstanceOf[IFormula]

  private object MulConverter extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(f, _) => (TheoryRegistry lookupSymbol f) match {
        case Some(mulTheory : MulTheory) if (f == mulTheory.mul && f != mul) =>
          IFunApp(mul, for (e <- subres.toList) yield e.asInstanceOf[ITerm])
        case _ =>
          t update subres
      }
      case _ =>
        t update subres
    }
  }
}
