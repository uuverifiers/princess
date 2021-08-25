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

  private val rewritings =
    Rewriter.combineRewritings(Theory.postSimplifiers(theories))

  def apply(f : Conjunction,
            maskTheoryConjuncts : Boolean = false,
            simplify : Boolean            = false,
            simplifySplittingLimit : Int  = 0,
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
        new Simplifier(simplifySplittingLimit) {
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

  def processFormula(f : Conjunction) : IFormula =
    apply(f)

  def processModel(f : Conjunction) : IFormula =
    apply(f, maskTheoryConjuncts = true, int2TermTranslation = true)

  def processInterpolant(f : Conjunction) :IFormula=
    apply(f, simplify = true, int2TermTranslation = true,
          simplifySplittingLimit = 20)

  def processConstraint(f : Conjunction) : IFormula=
    apply(f, simplify = true, int2TermTranslation = true)

  private def filterNonTheoryParts(model : Conjunction) : Conjunction = {
    implicit val _ = model.order
    val remainingPredConj = model.predConj filter {
      a => (TheoryRegistry lookupSymbol a.pred).isEmpty
    }
    model.updatePredConj(remainingPredConj)
  }

}
