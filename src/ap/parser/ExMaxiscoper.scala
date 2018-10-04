/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier
import ap.util.Debug

import IBinJunctor._
import Quantifier._

/**
 * Simple class for pulling out EX quantifiers from a formula.
 */
object ExMaxiscoper {

  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : IFormula =
    Rewriter.rewrite(Transform2NNF(f), rewriteVal).asInstanceOf[IFormula]

  private def rewriteFun(t : IExpression) : IExpression = t match {
    case IBinFormula(Or, IQuantified(EX, f1), IQuantified(EX, f2)) =>
      IQuantified(EX, IBinFormula(Or, f1, f2))
    case IBinFormula(j, IQuantified(EX, f1), f2) =>
      IQuantified(EX, IBinFormula(j, f1, VariableShiftVisitor(f2, 0, 1)))
    case IBinFormula(j, f2, IQuantified(EX, f1)) =>
      IQuantified(EX, IBinFormula(j, VariableShiftVisitor(f2, 0, 1), f1))
    case t => t
  }

  private val rewriteVal = rewriteFun _

}