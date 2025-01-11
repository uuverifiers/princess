/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.api

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{ADT, TheoryRegistry}
import ap.theories.bitvectors.ModuloArithmetic

  /**
   * Class representing (usually partial) models of formulas computed
   * through the API. Partial models represent values/individuals as
   * constructor terms, in case of integers as instances of <code>IIntLit</code>
   */
  class PartialModel(
         val interpretation : scala.collection.Map[IExpression, IExpression]) {

    import IExpression._

    /**
     * Locations on which this model is defined.
     */
    def definedLocations = interpretation.keySet

    /**
     * Evaluate an expression to some value in the current model, if possible.
     */
    def evalExpression(e : IExpression) : Option[IExpression] =
      Evaluator(e)

    /**
     * Evaluate a term to its internal integer representation in the model,
     * if possible.
     */
    def eval(t : ITerm) : Option[IdealInt] =
      for (EncodedInt(v) <- evalExpression(t)) yield v

    /**
     * Evaluate a term to a constructor term in the model, if possible.
     */
    def evalToTerm(t : ITerm) : Option[ITerm] =
      for (s <- evalExpression(t); if s.isInstanceOf[ITerm])
      yield s.asInstanceOf[ITerm]

    /**
     * Evaluate a formula to a truth value, if possible.
     */
    def eval(f : IFormula) : Option[Boolean] =
      for (IBoolLit(b) <- evalExpression(f)) yield b

    override def toString =
      "{" +
      (for ((l, v) <- interpretation.iterator)
       yield ("" + l + " -> " + v)).mkString(", ") +
      "}"

    ////////////////////////////////////////////////////////////////////////////

    private def toCtorTerm(t : ITerm, s : Sort) : ITerm = t match {
      case IIntLit(v) => s.decodeToTerm(v, Map()) getOrElse t
      case t          => t
    }

    private object EncodedInt {
      def unapply(t : IExpression) : Option[IdealInt] = t match {
        case IIntLit(v) =>
          Some(v)
        case ADT.BoolADT.True =>
          Some(IdealInt.ZERO)
        case ADT.BoolADT.False =>
          Some(IdealInt.ONE)
        case IFunApp(ModuloArithmetic.mod_cast,
                     Seq(Const(lower), Const(upper), Const(value))) =>
          Some(ModuloArithmetic.evalModCast(lower, upper, value))
        case t@IFunApp(f, _) =>
          // check whether some theory can turn the term into an int
          for (theory <- TheoryRegistry lookupSymbol f;
               IIntLit(v) <- theory evalFun t)
          yield v
        case _ =>
          None
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    private object Evaluator
            extends CollectingVisitor[Unit, Option[IExpression]] {
      def apply(t : IExpression) = visit(t, ())

      override def preVisit(t : IExpression,
                            arg : Unit) : PreVisitResult = t match {
        // handle equations directly, since we might not be able to
        // compute the difference between two constructor tems
        case Eq(left, right) =>
          ShortCutResult(
            for (l <- apply(left); r <- apply(right))
            yield IBoolLit((l, r) match {
                             case (EncodedInt(lv), EncodedInt(lr)) => lv == lr
                             case _ => l == r
                           }))
        case _ =>
          KeepArg
      }

      def postVisit(t : IExpression, arg : Unit,
                    subres : Seq[Option[IExpression]]) = t match {
        ////////////////////////////////////////////////////////////////////////
        // Terms

        case t : IIntLit =>
          Some(t)
        case t : IConstant =>
          interpretation get t
        case ITimes(coeff, _) =>
          for (EncodedInt(v) <- subres(0)) yield IIntLit(v * coeff)
        case _ : IPlus =>
          for (EncodedInt(v1) <- subres(0); EncodedInt(v2) <- subres(1))
          yield IIntLit(v1 + v2)

        case t@IFunApp(f, _) =>
          if (subres exists (_.isEmpty)) {
            None
          } else {
            val actualArgs = subres map (_.get.asInstanceOf[ITerm])
            val ctorF = t update actualArgs

            (interpretation get ctorF) orElse
            (for (theory <- TheoryRegistry lookupSymbol f;
                  res <- theory evalFun ctorF)
             yield toCtorTerm(res, Sort sortOf t))
          }

        case _ : ITermITE =>
          for (IBoolLit(b) <- subres(0);
               r <- subres(if (b) 1 else 2)) yield r

        ////////////////////////////////////////////////////////////////////////
        // Formulas

        case f : IBoolLit =>
          Some(f)
        case _ : INot =>
          for (IBoolLit(b) <- subres(0)) yield IBoolLit(!b)
        case IBinFormula(IBinJunctor.And, _, _) => subres match {
          case Seq(v@Some(IBoolLit(false)), _) => v
          case Seq(_, v@Some(IBoolLit(false))) => v
          case Seq(Some(IBoolLit(true)), v)    => v
          case Seq(v, Some(IBoolLit(true)))    => v
          case _                               => None
        }
        case IBinFormula(IBinJunctor.Or, _, _) => subres match {
          case Seq(v@Some(IBoolLit(true)), _) => v
          case Seq(_, v@Some(IBoolLit(true))) => v
          case Seq(Some(IBoolLit(false)), v)  => v
          case Seq(v, Some(IBoolLit(false)))  => v
          case _                              => None
        }
        case IBinFormula(IBinJunctor.Eqv, _, _) =>
          for (IBoolLit(v1) <- subres(0); IBoolLit(v2) <- subres(1))
          yield IBoolLit(v1 == v2)

        case f@IAtom(p, _) =>
          if (subres exists (_.isEmpty)) {
            None
          } else {
            val actualArgs = subres map (_.get.asInstanceOf[ITerm])
            val ctorF = f update actualArgs

            (interpretation get ctorF) orElse
            (for (theory <- TheoryRegistry lookupSymbol p;
                  res <- theory evalPred ctorF) yield res)
          }

        case IIntFormula(IIntRelation.EqZero, _) =>
          for (EncodedInt(v) <- subres(0)) yield IBoolLit(v.isZero)
        case IIntFormula(IIntRelation.GeqZero, _) =>
          for (EncodedInt(v) <- subres(0)) yield IBoolLit(v.signum >= 0)
        case _ : IFormulaITE =>
          for (IBoolLit(b) <- subres(0);
               r <- subres(if (b) 1 else 2)) yield r
        case _ : INamedPart =>
          subres(0)
      }
    }
  }
