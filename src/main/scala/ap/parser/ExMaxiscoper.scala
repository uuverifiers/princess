/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2023 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.conjunctions.Quantifier
import ap.util.Debug

import IBinJunctor._
import Quantifier._

/**
 * Simple class for pulling out EX quantifiers from a formula.
 */
object ExMaxiscoper {

  import IExpression.{Divisibility, NonDivisibility}

  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : IFormula =
    Rewriter.rewrite(Transform2NNF(f), rewriteVal).asInstanceOf[IFormula]

  private def rewriteFun(t : IExpression) : IExpression = t match {
    case IBinFormula(Or,
                     g1@ISortedQuantified(EX, sort1, f1),
                     g2@ISortedQuantified(EX, sort2, f2))
        if sort1 == sort2 &&
           Divisibility.unapply(g1).isEmpty &&
           Divisibility.unapply(g2).isEmpty =>
      ISortedQuantified(EX, sort1, IBinFormula(Or, f1, f2))
    case IBinFormula(j, g1@ISortedQuantified(EX, sort, f1), f2)
        if Divisibility.unapply(g1).isEmpty =>
      ISortedQuantified(EX, sort,
                        IBinFormula(j, f1, VariableShiftVisitor(f2, 0, 1)))
    case IBinFormula(j, f2, g1@ISortedQuantified(EX, sort, f1))
        if Divisibility.unapply(g1).isEmpty =>
      ISortedQuantified(EX, sort,
                        IBinFormula(j, VariableShiftVisitor(f2, 0, 1), f1))
    case t => t
  }

  private val rewriteVal = rewriteFun _

}
