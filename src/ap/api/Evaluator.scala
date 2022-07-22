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

package ap.api

import ap.parser._
import ap.basetypes.IdealInt
import ap.terfor.TerForConvenience
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.Atom
import ap.util.Debug

import SimpleAPI._

import scala.collection.mutable.ArrayBuffer

object Evaluator {

  private val AC = Debug.AC_SIMPLE_API

  private val satLikeStatus = Set(ProverStatus.Sat,
                                  ProverStatus.Invalid,
                                  ProverStatus.Inconclusive)

  import IExpression._

  private abstract class EvalResult {
    def toFormula : IFormula
  }

  private case class FormulaEvalResult(f : IFormula, value : Boolean)
                     extends EvalResult {
    def toFormula : IFormula = f <===> value
  }

  private case class TermEvalResult(t : ITerm, value : ITerm)
                     extends EvalResult {
    def toFormula : IFormula = t === value
  }

  private case class IntTermEvalResult(t : ITerm, value : IdealInt)
                     extends EvalResult {
    def toFormula : IFormula = t === value
  }

  class UnknownTermValueException(t : ITerm)
        extends SimpleAPI.SimpleAPIException(
    "Due to quantifiers, term " + t + " cannot be evaluated")

}

class Evaluator(api : SimpleAPI) {

  import Evaluator._

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertPre(AC, satLikeStatus(api.getStatus(false)),
                  "Complete model can only be extracted after SAT result")
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /*
  def getPartialModel                   : Conjunction
  def getFullModel                      : Conjunction
  def getCurrentStatus                  : ProverStatus.Value
  def toInternal(f : IFormula)          : Conjunction
  def addModelRestriction(f : IFormula) : Unit
  def pushModelRestrictionFrame         : Unit
  def popModelRestrictionFrame          : Unit
  def createFreshRelation(arity : Int)  : IExpression.Predicate
  def checkSatHelp(block : Boolean,
                   allowShortCut : Boolean) : ProverStatus.Value
   */


  //////////////////////////////////////////////////////////////////////////////

  /**
   * During evaluation, we might have to extend a partial model, which
   * requires re-running the prover. To make sure that evaluation
   * never produces inconsistent results, we log all results produced
   * by evaluation, and add those results as additional assumptions to
   * the prover when extending a model.
   */
  private val evalResults = new ArrayBuffer[EvalResult]

  private var extendingModel : Boolean = false

  private def ensureExtendingModel = {
    if (!extendingModel) {
      api.push
      extendingModel = true
    }

    for (result <- evalResults)
      api.addAssertion(result.toFormula)
    evalResults.clear
  }

  def resetModelExtension = {
    if (extendingModel) {
      api.pop
      extendingModel = false
    }

    evalResults.clear
  }

  //////////////////////////////////////////////////////////////////////////////

  def evalToInt(t : ITerm) : IdealInt =
    evalPartialToInt(t) match {

      case Some(res) => res

      case None => {
        // then we have to extend the model

        ensureExtendingModel

        import TerForConvenience._

        if (api.needsExhaustiveProver) {
          // TODO

          throw new UnknownTermValueException(t)

        } else {

          // TODO: special cases

          import IExpression._

          val x = api.createConstant("x")
          println("forcing decision: " + (x === t))
          api.addAssertion(x === t)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !api.needsExhaustiveProver)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          api.??? match {
            case s if satLikeStatus(s) =>
              evalToInt(x)
            case _ =>
              throw NoModelException
          }
        }
      }
    }

  def evalToTerm(t : ITerm) : ITerm =
    evalPartialToTerm(t) match {
      case Some(res) => res

      case None => {
        // then we have to extend the model

        ensureExtendingModel

        import TerForConvenience._

        if (api.needsExhaustiveProver) {
          // TODO

          throw new UnknownTermValueException(t)

        } else {

          // TODO: special cases

          import IExpression._

          val x = api.createConstant("x", Sort sortOf t)
          println("forcing decision: " + (x === t))
          api.addAssertion(x === t)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !api.needsExhaustiveProver)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          api.??? match {
            case s if satLikeStatus(s) =>
              evalToTerm(x)
            case _ =>
              throw NoModelException
          }
        }
      }
    }

  def evalToBool(f : IFormula) : Boolean =
    evalPartialToBool(f) match {

      case Some(res) => res

      case None => {
        // then we have to extend the model

        ensureExtendingModel

        import TerForConvenience._

        if (api.needsExhaustiveProver) {
          // then we have to re-run the prover to check whether the
          // given formula is consistent with our assertions

          evalToBoolExhaustiveProver(f)

        } else {

          // TODO: special cases

          import IExpression._

          val p = api.createBooleanVariable("p")
          println("forcing decision: " + (f <=> p))
          api.addAssertion(f <=> p)

          if (api.needsExhaustiveProver) {
            evalToBoolExhaustiveProver(p)
          } else {
            api.??? match {
              case s if satLikeStatus(s) =>
                evalToBool(p)
              case _ =>
                throw NoModelException
            }
          }
        }
      }
    }

  private def evalToBoolExhaustiveProver(f : IFormula) : Boolean = {
    api.push

    val res =
      try {
        api.addAssertion(f)
        api.??? match {
          case s if satLikeStatus(s) =>
            true
          case ProverStatus.Unsat | ProverStatus.Valid =>
            false
          case _ =>
            throw NoModelException
        }
      } finally {
        api.pop
      }

    evalResults += FormulaEvalResult(f, res)

    res
  }

  private def evalPartialToInt(t : ITerm) : Option[IdealInt] =
    api.evalPartial(t) match {
      case Some(res) => {
        evalResults += IntTermEvalResult(t, res)
        Some(res)
      }
      case None =>
        None
    }

  private def evalPartialToTerm(t : ITerm) : Option[ITerm] =
    api.evalPartialAsTerm(t) match {
      case Some(res) => {
        evalResults += TermEvalResult(t, res)
        Some(res)
      }
      case None =>
        None
    }

  private def evalPartialToBool(f : IFormula) : Option[Boolean] =
    api.evalPartial(f) match {
      case Some(res) => {
        evalResults += FormulaEvalResult(f, res)
        Some(res)
      }
      case None =>
        None
    }

}
