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

}

abstract class Evaluator(api : SimpleAPI) {

  import Evaluator._
  import api.{reducerSettings, order, pushHelp, popHelp,
              addFormulaHelp, addRelationHelp, checkSatHelp}

  def getPartialModel          : Conjunction
  def getFullModel             : Conjunction
  def getCurrentStatus         : ProverStatus.Value
  def toInternal(f : IFormula) : Conjunction

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
      pushHelp
      extendingModel = true
    }

    for (result <- evalResults)
      addFormulaHelp(!result.toFormula)
    evalResults.clear
  }

  def resetModelExtension = {
    if (extendingModel) {
      popHelp
      extendingModel = false
    }

    evalResults.clear
  }

  //////////////////////////////////////////////////////////////////////////////

  def evalToInt(t : ITerm)     : IdealInt = 0

  def evalToTerm(t : ITerm)    : ITerm = null

  def evalToBool(f : IFormula) : Boolean = {
    /*
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + eval(")
      PrettyScalaLineariser(getFunctionNames)(f)
      println("))")
    }
     */

    evalPartialHelp(f) match {

      case Left(res) => res

      case Right(_) => {
        // then we have to extend the model

        import TerForConvenience._

        if (api.apiStack.needExhaustiveProver) {
          // then we have to re-run the prover to check whether the
          // given formula is consistent with our assertions

          false // TODO
        } else {

          // TODO: special cases

          import IExpression._

          ensureExtendingModel

          val p = new IExpression.Predicate("p", 0)
          addRelationHelp(p)
          addFormulaHelp(f </> p())

          checkSatHelp(true, true)
          evalPartialToBoolHelp(p()).get // TODO: this won't work if we now need the exhaustive prover

        }
      }
    }
  }

  def evalPartialToInt(t : ITerm)     : Option[IdealInt] = None

  def evalPartialToTerm(t : ITerm)    : Option[ITerm] = None

  def evalPartialToBool(f : IFormula) : Option[Boolean] = {
    /*
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + evalPartial(")
      PrettyScalaLineariser(getFunctionNames)(f)
      println("))")
    }
     */

    evalPartialToBoolHelp(f)
  }

  private def evalPartialToBoolHelp(f : IFormula) : Option[Boolean] =
    evalPartialHelp(f) match {
      case Left(res) => {
        evalResults += FormulaEvalResult(f, res)
        Some(res)
      }
      case Right(_) => None
    }

  //////////////////////////////////////////////////////////////////////////////

  private def evalPartialHelp(f : IFormula) : Either[Boolean,Conjunction] = {
    import TerForConvenience._

    /*
    doDumpSMT {
      print("(get-value (")
      SMTLineariser(f)
      println("))")
    }
     */
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, satLikeStatus(getCurrentStatus))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    f match {
      case IAtom(p, args) if (args forall (_.isInstanceOf[IIntLit])) => {
        val pModel = getPartialModel
        val a = Atom(p, for (IIntLit(value) <- args)
                        yield l(value), order)

        if (pModel == null)
          Right(a)
        else if (pModel.predConj.positiveLitsAsSet contains a)
          Left(true)
        else if (pModel.predConj.negativeLitsAsSet contains a)
          Left(false)
        else {
          val fModel = getFullModel
          if (pModel != fModel) {
            if (fModel.predConj.positiveLitsAsSet contains a)
              Left(true)
            else if (fModel.predConj.negativeLitsAsSet contains a)
              Left(false)
            else
              Right(a)
          } else {
            Right(a)
          }
        }
      }
      case _ => {
        // more complex check by reducing the expression via the model
        val fModel = getFullModel
        val intF   = toInternal(f)

        if (fModel == null) {
          Right(intF)
        } else {
          val reduced = ReduceWithConjunction(fModel, fModel.order,
                                              reducerSettings)(intF)

          if (reduced.isTrue)
            Left(true)
          else if (reduced.isFalse)
            Left(false)
          else
            Right(intF)
        }
      }
    }
  }

}
