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
        case (s ::: ModSort(_, _), t ::: Numeric(_)) =>
          cast2Int(s) === t
        case (s ::: Numeric(_), t ::: ModSort(_, _)) =>
          s === cast2Int(t)
        case _ =>
          t update subres
      }
    case _ =>
      t update subres
  }

}
