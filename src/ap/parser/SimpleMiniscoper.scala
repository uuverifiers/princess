/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.terfor.conjunctions.Quantifier
import ap.util.Debug

import IBinJunctor._
import Quantifier._

/**
 * Simple class for pushing down blocks of EX quantifiers;
 * turn EX x. (phi | psi) into (EX x. phi) | (EX x. psi)
 */
class SimpleMiniscoper(signature : Signature) {

  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : IFormula =
    Rewriter.rewrite(Transform2NNF(f), rewriteVal).asInstanceOf[IFormula]

  private def rewriteFun(t : IExpression) : IExpression = t match {
    case IBinFormula(And,
                     g@IAtom(p, Seq(_ : IVariable)),
                     IBinFormula(Or, f1, f2))
        if (signature.domainPredicates contains p) =>
      IBinFormula(Or, IBinFormula(And, g, f1), IBinFormula(And, g, f2))
    case IQuantified(EX, IBinFormula(Or, f1, f2)) =>
      IBinFormula(Or, IQuantified(EX, f1), IQuantified(EX, f2))
    case t => t
  }

  private val rewriteVal = rewriteFun _

}