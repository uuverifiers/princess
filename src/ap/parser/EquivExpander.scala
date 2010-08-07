/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier

/**
 * Class to turn <-> into conjunction and disjunctions
 */
object EquivExpander extends ContextAwareVisitor[Unit, IExpression] {

  import IExpression._
  
  def apply(f : IFormula) : IFormula =
    this.visit(f, Context()).asInstanceOf[IFormula]
  
  override def preVisit(t : IExpression, c : Context[Unit]) : PreVisitResult =
    t match {
      case LeafFormula(_) | _ : ITerm =>
        // do not look into atoms or terms
        ShortCutResult(t)
      case IBinFormula(IBinJunctor.Eqv, f1, f2) =>
        if ((c.quans contains Quantifier.EX) ^ (c.polarity < 0))
          TryAgain((f1 & f2) | (!f1 & !f2), c)
        else
          TryAgain((f1 ==> f2) & (f2 ==> f1), c)
      case _ =>
        super.preVisit(t, c)
    }

  def postVisit(t : IExpression, c : Context[Unit],
                subres : Seq[IExpression]) : IExpression =
    t update subres

}
