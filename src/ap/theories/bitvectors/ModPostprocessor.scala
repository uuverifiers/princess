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
import ap.theories._
import ap.types.{SortedIFunction, SortedPredicate}

/**
 * Post-processing of bit-vector formulas to make them correctly typed.
 */
object ModPostprocessor
       extends CollectingVisitor[IExpression.Sort, IExpression] {

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
    case _ : IConstant | _ : IFunApp => {
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

}
