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

/**
 * A class representing a first-order model of some formula. The class
 * will internally start from the partial model computed by a
 * <code>SimpleAPI</code>, and extend this model on demand. The class
 * will make use of the <code>SimpleAPI</code> instance to compute
 * missing parts of the model, and can therefore mutate the state of
 * the <code>SimpleAPI</code>. To reset the <code>SimpleAPI</code> to
 * the state before creating the <code>Evaluator</code>, use the
 * method <code>resetModelExtension</code>; a safer way is to apply
 * the method <code>SimpleAPI.withCompleteModel</code> to spawn the
 * <code>Evaluator</code>.
 */
class Evaluator(api : SimpleAPI) {

  import Evaluator._

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertPre(AC, satLikeStatus(api.getStatus(false)),
                  "Complete model can only be extracted after SAT result")
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

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
      api.evaluatorStarted
      api.push
      extendingModel = true
    }

    for (result <- evalResults)
      api.addAssertion(result.toFormula)
    evalResults.clear
  }

  /**
   * Reset the evaluator and the connected <code>SimpleAPI</code> instance.
   */
  def shutDown = {
    if (extendingModel) {
      api.pop
      extendingModel = false
      api.evaluatorStopped
    }

    evalResults.clear
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Evaluate a term to an integer. This method should be used for
   * integer or bit-vector terms, but can in principle be applied to
   * any term.
   */
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
//          println("forcing decision: " + (x === t))
          api.addAssertion(x === t)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !api.needsExhaustiveProver)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          api.checkSat(true) match {
            case s if satLikeStatus(s) =>
              evalToInt(x)
            case _ =>
              throw NoModelException
          }
        }
      }
    }

  /**
   * Evaluate a term to a constructor term. This method has the same effect
   * as <code>evalToTerm</code>.
   */
  def apply(t : ITerm) : ITerm = evalToTerm(t)

  /**
   * Evaluate a term to a constructor term.
   */
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
//          println("forcing decision: " + (x === t))
          api.addAssertion(x === t)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !api.needsExhaustiveProver)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          api.checkSat(true) match {
            case s if satLikeStatus(s) =>
              evalToTerm(x)
            case _ =>
              throw NoModelException
          }
        }
      }
    }

  /**
   * Evaluate a formula to a Boolean. This method has the same effect
   * as <code>evalToBool</code>.
   */
  def apply(f : IFormula) : Boolean = evalToBool(f)

  /**
   * Evaluate a formula to a Boolean.
   */
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
//          println("forcing decision: " + (f <=> p))
          api.addAssertion(f <=> p)

          if (api.needsExhaustiveProver) {
            evalToBoolExhaustiveProver(p)
          } else {
            api.checkSat(true) match {
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
        api.checkSat(true) match {
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
