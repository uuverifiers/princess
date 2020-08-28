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

package ap.parser

import ap.Signature
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.theories.{Theory, TheoryRegistry}
import ap.types.IntToTermTranslator

import scala.collection.{Map => GMap}

/**
 * Postprocess a formula output by the prover, for instance a model or the
 * result of interpolation or quantifier elimination.
 */
class Postprocessing(signature : Signature,
                     predTranslation : GMap[Predicate, IFunction]) {

  private val theories = signature.theories
  private val order    = signature.order

  def apply(f : Conjunction,
            maskTheoryConjuncts : Boolean = false,
            simplify : Boolean            = false,
            int2TermTranslation : Boolean = false) : IFormula = {

    var formula = f

    if (maskTheoryConjuncts)
      formula = filterNonTheoryParts(formula)

    formula = Theory.postprocess(formula, theories, order)

    var iFormula = Internal2InputAbsy(formula, predTranslation)

    iFormula = Theory.iPostprocess(iFormula, theories, signature)

    iFormula = VariableSortInferenceVisitor(iFormula)

    if (simplify) {
      val simplifier =
        new Simplifier {
          private val rewritings =
            Rewriter.combineRewritings(Theory.postSimplifiers(theories))
          protected override def furtherSimplifications(expr : IExpression) =
            rewritings(expr)
        }
      iFormula = simplifier(iFormula)
    }

    if (int2TermTranslation) {
      implicit val context = new Theory.DefaultDecoderContext(f)
      iFormula = IntToTermTranslator(iFormula)
    }

    iFormula

  }

  def processModel(f : Conjunction) : IFormula =
    apply(f, maskTheoryConjuncts = true, int2TermTranslation = true)

  def processInterpolant(f : Conjunction) :IFormula=
    apply(f, simplify = true, int2TermTranslation = true)

  def processConstraint(f : Conjunction) : IFormula=
    apply(f)

  private def filterNonTheoryParts(model : Conjunction) : Conjunction = {
    implicit val _ = model.order
    val remainingPredConj = model.predConj filter {
      a => (TheoryRegistry lookupSymbol a.pred).isEmpty
    }
    model.updatePredConj(remainingPredConj)
  }

}
