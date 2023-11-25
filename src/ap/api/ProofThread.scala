/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2023 Philipp Ruemmer <ph_r@gmx.net>
 *               2023      Amanda Stjerna <amanda.stjerna@it.uu.se>
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

import ap.proof.{ExhaustiveProver, ModelSearchProver}
import ap.terfor.conjunctions.Conjunction
import ap.proof.certificates.{Certificate, LemmaBase}
import ap.terfor.TermOrder
import ap.parameters.{GoalSettings, Param}
import ap.util.{Debug, Timeout}

import java.util.concurrent.LinkedBlockingQueue

object ProofThreadRunnable {

  private val AC = Debug.AC_SIMPLE_API

  abstract class ProverCommand

  case class CheckSatCommand(prover : ModelSearchProver.IncProver,
                             needLemmaBase : Boolean,
                             reuseLemmaBase : Boolean)
             extends ProverCommand
  case class CheckValidityCommand(formula : Conjunction,
                                  goalSettings : GoalSettings,
                                  mostGeneralConstraint : Boolean)
             extends ProverCommand
  case object NextModelCommand extends ProverCommand
  case class  AddFormulaCommand(formula : Conjunction) extends ProverCommand
  case object RecheckCommand extends ProverCommand
  case object DeriveFullModelCommand extends ProverCommand
  case object ShutdownCommand extends ProverCommand

  abstract class ProverResult
  case object UnsatResult extends ProverResult
  case class  FoundConstraintResult(constraint : Conjunction,
                                    model : Conjunction)
              extends ProverResult
  case class  UnsatCertResult(cert : Certificate) extends ProverResult
  case object InvalidResult extends ProverResult
  case class SatResult(model : Conjunction) extends ProverResult
  case class SatPartialResult(model : Conjunction) extends ProverResult
  case object StoppedResult extends ProverResult
  case class ExceptionResult(t : Throwable) extends ProverResult
  case object OutOfMemoryResult extends ProverResult

}

class ProofThreadRunnable(
         proverCmd : LinkedBlockingQueue[ProofThreadRunnable.ProverCommand],
         proverRes : LinkedBlockingQueue[ProofThreadRunnable.ProverResult],
         enableAssert : Boolean,
         logging      : Set[Param.LOG_FLAG]) extends Runnable {
  import ProofThreadRunnable._

  private var stopProofTaskVar = false

  def stopProofTask      = (stopProofTaskVar = true)
  def resetStopProofTask = (stopProofTaskVar = false)

  def run : Unit = {
    Debug enableAllAssertions enableAssert
    
    var cont = true
    var nextCommand : ProverCommand = null
    var lemmaBase : LemmaBase = null
    
    def directorWaitForNextCmd(order : TermOrder) = {
      var res : ModelSearchProver.SearchDirection = null
      var forsToAdd = List[Conjunction]()
              
      while (res == null) proverCmd.take match {
        case DeriveFullModelCommand =>
          res = ModelSearchProver.DeriveFullModelDir
        case NextModelCommand =>
          res = ModelSearchProver.NextModelDir
        case RecheckCommand =>
          res = ModelSearchProver.AddFormulaDir(
                 Conjunction.disj(forsToAdd, order))
        case AddFormulaCommand(formula) =>
          forsToAdd = formula :: forsToAdd
        case c : ProverCommand => {
          // get out of here, terminate the <code>ModelSearchProver</code> run
          nextCommand = c
          res = ModelSearchProver.ReturnSatDir
        }
      }
              
      res
    }
    
    val commandParser : PartialFunction[Any, Unit] = {
      case CheckSatCommand(p, needLemmaBase, reuseLemmaBase) => {

        if (needLemmaBase) {
          if (lemmaBase == null || !reuseLemmaBase) {
            val printL = logging contains Param.LOG_LEMMAS
            lemmaBase = new LemmaBase(printLemmas = printL)
          } else {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, lemmaBase.hasEmptyStack)
            //-END-ASSERTION-///////////////////////////////////////////////////
          }
        } else {
          lemmaBase = null
        }

        Timeout.catchTimeout {
          val order = p.order

          p.checkValidityDir({
            case (model, false) => {
              proverRes put SatPartialResult(model)
              directorWaitForNextCmd(order)
            }
            
            case (model, true) => {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertPre(AC, !model.isFalse)
              //-END-ASSERTION-/////////////////////////////////////////////////
              
              proverRes put SatResult(model)
              directorWaitForNextCmd(order)
            }
          }, lemmaBase)
        } { case _ => null } match {

          case null =>
            proverRes put StoppedResult
          case Left(m) if (nextCommand == null) =>
            proverRes put UnsatResult
          case Left(_) =>
            // nothing
          case Right(cert) =>
            proverRes put UnsatCertResult(cert)
              
        }
      }

      case CheckValidityCommand(formula, goalSettings, mgc) => {
        
        lemmaBase = null

        Timeout.catchTimeout {
          
          val prover = new ExhaustiveProver (!mgc, goalSettings)
          val tree = prover(formula, formula.order)
          tree.closingConstraint
          
        } { case _ => null } match {
          
          case null =>
            proverRes put StoppedResult
          case constraint =>
            if (constraint.isFalse) {
              proverRes put InvalidResult
            } else {
              val solution =
                ModelSearchProver(constraint.negate, constraint.order)
              proverRes put FoundConstraintResult(constraint, solution)
            }
            
        }
      }

      case ShutdownCommand =>
        cont = false
    }
    
    Timeout.withChecker(() => if (stopProofTaskVar) Timeout.raise) {
      while (cont)
        try {
          stopProofTaskVar = false

          // wait for a command on what to do next
          if (nextCommand != null) {
            val c = nextCommand
            nextCommand = null
            commandParser(c)
          } else {
            commandParser(proverCmd.take)
          }
        } catch {
          case t : Timeout =>
            // just forward
            throw t
          case _ : StackOverflowError | _ : OutOfMemoryError =>
            // hope that we are able to continue
            proverRes put OutOfMemoryResult
          case _ : NoClassDefFoundError =>
            // this exception indicates a stack overflow as well,
            // but probably the system has to be restarted at this point
            proverRes put OutOfMemoryResult
          case t : InterruptedException =>
            // somebody interrupted the thread, we assume that it is
            // supposed to die
            cont = false
          case t : Throwable =>
            // hope that we are able to continue
            proverRes put ExceptionResult(t)
        }
      
    }
  }
}
