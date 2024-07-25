/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.basetypes.IdealInt
import ap.parser._
import ap.types.{Sort, MonoSortedIFunction}
import ap.theories.rationals.Rationals
import ap.terfor.conjunctions.Conjunction

object DivZero {

  val IntDivZeroTheory =
    new DivZero("IntDivZero",
                List(("intDivZero", Sort.Integer),
                     ("intModZero", Sort.Integer)))

  /**
   * Uninterpreted function representing the SMT-LIB integer division
   * by zero.
   */
  val IntDivZero = IntDivZeroTheory.functions(0)

  /**
   * Uninterpreted function representing the SMT-LIB integer modulo
   * zero operation.
   */
  val IntModZero = IntDivZeroTheory.functions(1)

  def handleZero(normalOp : (ITerm, ITerm) => ITerm,
                 zeroFun  : IFunction,
                 zero     : ITerm,
                 sort     : Sort)
                (num : ITerm, denom : ITerm) : ITerm = {
    import IExpression._

    denom match {
      case Const(IdealInt.ZERO) =>
        zeroFun(num)
      case Const(_) =>
        normalOp(num, denom)
      case SimpleTerm(_) if isSimpleTerm(num) =>
        ite(denom === zero, zeroFun(num), normalOp(num, denom))
      case _ => {
        val res    = v(2, sort)
        val numV   = v(1, sort)
        val denomV = v(0, sort)

        sort.eps(sort.ex(sort.ex(
                           numV === shiftVars(num, 0, 3) &
                             denomV === shiftVars(denom, 0, 3) &
                             res === ite(denomV === zero,
                                         zeroFun(numV),
                                         normalOp(numV, denomV))
                         )))
      }
    }
  }

}

/**
 * Theory representing the SMT-LIB semantics of division and modulo by
 * zero. According to SMT-LIB, division is a total function, and
 * division by zero has to be represented as a unary uninterpreted
 * function.
 */
class DivZero(name : String,
              consideredFunctions : Seq[(String, Sort)]) extends Theory {

  val functions =
    for ((name, sort) <- consideredFunctions.toIndexedSeq)
    yield MonoSortedIFunction(name, List(sort), sort, true, false)

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  val totalityAxioms = Conjunction.TRUE

  val functionalPredicates: Set[ap.parser.IExpression.Predicate] =
    predicates.toSet

  val functionPredicateMapping =
    functions zip (functions map functionTranslation)

  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  val plugin = None

  override def isSoundForSat(
         theories : Seq[Theory],
         config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary
         | Theory.SatSoundnessConfig.Existential =>
        true
      case Theory.SatSoundnessConfig.General =>
        false
    }

  override def toString = name

  TheoryRegistry register this

}

