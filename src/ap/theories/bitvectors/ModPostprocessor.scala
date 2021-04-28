/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2021 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.parser._
import ap.theories._
import ap.types.{SortedIFunction, SortedPredicate}
import ap.util.Debug

/**
 * Post-processing of bit-vector formulas to make them correctly typed.
 */
object ModPostprocessor
       extends CollectingVisitor[IExpression.Sort, IExpression] {

  private val AC = Debug.AC_MODULO_ARITHMETIC

  import IExpression._
  import ModuloArithmetic._
  import Sort.{:::, Numeric}

  def apply(f : IFormula) : IFormula =
    visit(f, null).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        ctxt : Sort) : PreVisitResult = t match {
    case _ : IEquation =>
      UniSubArgs(null)
    case Eq(left, right) =>
      TryAgain(IEquation(left, right), null)
    case _ : IPlus | _ : ITimes | _ : IIntFormula =>
      UniSubArgs(Sort.Integer)
    case _ : ITermITE =>
      SubArgs(Array(null, ctxt, ctxt))
    case IFunApp(`bv_extract`, _) =>
      SubArgs(Array(Sort.Integer, Sort.Integer, null))
    case IFunApp(f, args) =>
      SubArgs(SortedIFunction.iArgumentSorts(f, args))
    case IAtom(p, args) =>
      SubArgs(SortedPredicate.iArgumentSorts(p, args))
    case _ =>
      UniSubArgs(null)
  }

  def postVisit(t : IExpression,
                ctxt : Sort,
                subres : Seq[IExpression]) : IExpression = t match {
    case AtomicTerm(t) => {
      val newT = t.asInstanceOf[ITerm] update subres
      (Sort sortOf newT, ctxt) match {
        case (_, null)                   => newT
        case (ModSort(_, _), Numeric(_)) => cast2Int(newT)
        case _                           => newT
      }
    }
    case _ : IEquation =>
      (subres(0), subres(1)) match {
        case (t ::: ModSort(lower, upper), Const(value))
            if lower <= value && value <= upper =>
          t === cast2Interval(lower, upper, value)
        case (Const(value), t ::: ModSort(lower, upper))
            if lower <= value && value <= upper =>
          t === cast2Interval(lower, upper, value)
        case (s ::: (sSort : ModSort), t ::: (tSort : ModSort))
            if sSort != tSort =>
          cast2Int(s) === cast2Int(t)
          // TODO: insert this cast whenever t is a non-bitvector term?
        case (s ::: ModSort(_, _), t ::: Numeric(_)) =>
          cast2Int(s) === t
          // TODO: insert this cast whenever t is a non-bitvector term?
        case (s ::: Numeric(_), t ::: ModSort(_, _)) =>
          s === cast2Int(t)
        case _ =>
          t update subres
      }
    case _ =>
      t update subres
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Turn as sub-formulas, as far as possible, into pure formulas only
   * containing bit-vector operations; avoid the use of <code>int_cast</code>
   * in this case.
   */
  def purifyFormula(f : IFormula) : IFormula =
    Purifier.visit(f, ()).asInstanceOf[IFormula]

  private object Purifier extends CollectingVisitor[Unit, IExpression] {

    override def preVisit(t : IExpression,
                          ctxt : Unit) : PreVisitResult = t match {
      case Eq(left, right) => {
        val res =
          for (w1 <- BitWidthInferrer(left);
               w2 <- BitWidthInferrer(right);
               if left.isInstanceOf[IPlus] || right.isInstanceOf[IPlus];
               w = w1 max w2)
          yield TryAgain(IEquation(BitVectorPadder(left, w),
                                   BitVectorPadder(right, w)), ())

        res getOrElse KeepArg
      }

      case Geq(MaybeCastAtomicTerm(left ::: UnsignedBVSort(w)), Const(value))
          if value.signum >= 0 && value <= pow2MinusOne(w) =>
        TryAgain(IAtom(bv_ule, List(w, bv(w, value), left)), ())

      case Geq(Const(value), MaybeCastAtomicTerm(right ::: UnsignedBVSort(w)))
          if value.signum >= 0 && value <= pow2MinusOne(w) =>
        TryAgain(IAtom(bv_ule, List(w, right, bv(w, value))), ())

      case Geq(left, right) => {
        val res =
          for (w1 <- BitWidthInferrer(left);
               w2 <- BitWidthInferrer(right);
               w = w1 max w2)
          yield TryAgain(IAtom(bv_sle,
                               List(w,
                                    BitVectorPadder(right, w),
                                    BitVectorPadder(left, w))), ())
        res getOrElse KeepArg
      }

      case IIntFormula(IIntRelation.GeqZero, s) =>
        BitWidthInferrer(s) match {
          case Some(w) =>
            TryAgain(IAtom(bv_sle,
                           List(w, bv(w, 0), BitVectorPadder(s, w))), ())
          case None =>
            KeepArg
      }

      case IIntFormula(IIntRelation.EqZero, s) =>
        BitWidthInferrer(s) match {
          case Some(w) =>
            TryAgain(IEquation(BitVectorPadder(s, w), bv(w, 0)), ())
          case None =>
            KeepArg
        }

      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression,
                  ctxt : Unit,
                  subres : Seq[IExpression]) : IExpression =
      t update subres

  }

/*
    case _ : IEquation =>
      UniSubArgs(null)

    case Eq(left, right) =>
      (for (w1 <- BitWidthInferrer(left);
            w2 <- BitWidthInferrer(right);
            if left.isInstanceOf[IPlus] || right.isInstanceOf[IPlus];
            w = w1 max w2)
       yield TryAgain(IEquation(BitVectorPadder(left, w),
                                BitVectorPadder(right, w)), null)) getOrElse
      TryAgain(IEquation(left, right), null)

    case Geq(AtomicTerm(left ::: UnsignedBVSort(w)), Const(value))
        if value.signum >= 0 && value <= pow2MinusOne(w) =>
      TryAgain(IAtom(bv_ule, List(w, bv(w, value), left)), null)

    case Geq(Const(value), AtomicTerm(right ::: UnsignedBVSort(w)))
        if value.signum >= 0 && value <= pow2MinusOne(w) =>
      TryAgain(IAtom(bv_ule, List(w, right, bv(w, value))), null)

    case Geq(left, right) =>
      (for (w1 <- BitWidthInferrer(left);
            w2 <- BitWidthInferrer(right);
            w = w1 max w2)
       yield TryAgain(IAtom(bv_sle,
                            List(w,
                                 BitVectorPadder(right, w),
                                 BitVectorPadder(left, w))), null)) getOrElse
      UniSubArgs(Sort.Integer)

    case IIntFormula(IIntRelation.GeqZero, s) =>
      BitWidthInferrer(s) match {
        case Some(w) =>
          TryAgain(IAtom(bv_sle,
                         List(w, bv(w, 0), BitVectorPadder(s, w))), null)
        case None =>
          UniSubArgs(Sort.Integer)
      }

    case IIntFormula(IIntRelation.EqZero, s) =>
      BitWidthInferrer(s) match {
        case Some(w) =>
          TryAgain(IEquation(BitVectorPadder(s, w), bv(w, 0)), null)
        case None =>
          UniSubArgs(Sort.Integer)
      }
 */

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Infer the signed bit-vector format needed to perform some computation
   * without overflows.
   */
  private object BitWidthInferrer
                 extends CollectingVisitor[Unit, Option[Int]] {
    def apply(t : ITerm) : Option[Int] = visit(t, ())

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case MaybeCastAtomicTerm(t) =>
        ShortCutResult(
          (Sort sortOf t) match {
            case UnsignedBVSort(width) => Some(width + 1)
            case _                     => None
          }
        )
      case IIntLit(value) =>
        ShortCutResult(Some(bitWidth(value)))
      case IFunApp(`mod_cast`,
                   Seq(IIntLit(lower), IIntLit(upper), IIntLit(value))) =>
        ShortCutResult(Some(bitWidth(evalModCast(lower, upper, value))))
      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[Option[Int]]) : Option[Int] = t match {
      case t : IPlus =>
        for (left <- subres(0); right <- subres(1))
        yield ((left max right) + 1)
      case ITimes(coeff, _) =>
        for (bits <- subres(0))
        yield (bits + coeff.abs.getHighestSetBit)
      case _ =>
        None
    }
  }

  private def bitWidth(v : IdealInt) : Int = v match {
    case IdealInt.ZERO => 1
    case v             => v.abs.getHighestSetBit + 1
  }

  //////////////////////////////////////////////////////////////////////////////

  private object AtomicTerm {
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case t : IVariable => Some(t)
      case t : IConstant => Some(t)
      case t : IFunApp   => Some(t)
      case _             => None
    }
  }

  private object MaybeCastAtomicTerm {
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case IFunApp(`int_cast`, Seq(AtomicTerm(t))) => Some(t)
      case AtomicTerm(t)                           => Some(t)
      case _                                       => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object BitVectorPadder
                 extends CollectingVisitor[Int, ITerm] {
    def apply(t : ITerm, newWidth : Int) : ITerm = visit(t, newWidth)

    override def preVisit(t : IExpression,
                          newWidth : Int) : PreVisitResult = t match {
      case MaybeCastAtomicTerm(t) => {
        val UnsignedBVSort(oldWidth) = Sort sortOf t
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, oldWidth <= newWidth)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (oldWidth < newWidth)
          ShortCutResult(zero_extend(newWidth - oldWidth,
                                     t.asInstanceOf[ITerm]))
        else
          ShortCutResult(t.asInstanceOf[ITerm])
      }
      case t : IIntLit =>
        ShortCutResult(ModuloArithmetic.cast2UnsignedBV(newWidth, t))
      case IFunApp(`mod_cast`,
                   Seq(IIntLit(lower), IIntLit(upper), IIntLit(value))) =>
        ShortCutResult(bv(newWidth, evalModCast(lower, upper, value)))
      case _ =>
        KeepArg
    }
    def postVisit(t : IExpression,
                  newWidth : Int,
                  subres : Seq[ITerm]) : ITerm = t match {
      case _ : IPlus =>
        bvadd(subres(0), subres(1))
      case ITimes(IdealInt.MINUS_ONE, _) =>
        bvneg(subres(0))
      case ITimes(coeff, _) =>
        bvmul(ModuloArithmetic.cast2UnsignedBV(newWidth, coeff), subres(0))
    }
  }

}
