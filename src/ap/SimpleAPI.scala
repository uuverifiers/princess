/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.{TermOrder, ConstantTerm}
import ap.proof.ModelSearchProver
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.util.{Debug, Timeout}

import scala.collection.mutable.{HashMap => MHashMap, SynchronizedQueue,
                                 ArrayStack}
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.concurrent.SyncVar

object SimpleAPI {
  
  private val AC = Debug.AC_SIMPLE_API

  def spawn : SimpleAPI = new SimpleAPI
  
  object ProverStatus extends Enumeration {
    val Sat, Unsat, Unknown, Running, Error = Value
  }
  
  private abstract class ProverCommand

  private case class CheckSatCommand(prover : ModelSearchProver.IncProver)
          extends ProverCommand
  private case object ShutdownCommand extends ProverCommand
  private case object StopCommand extends ProverCommand

  private abstract class ProverResult
  private case object UnsatResult extends ProverResult
  private case class SatResult(model : Conjunction) extends ProverResult
  private case object StoppedResult extends ProverResult

}

/**
 * API that simplifies the use of the prover; this tries to collect various
 * functionality in one place, and provides an imperative API similar to the
 * SMT-LIB command language.
 */
class SimpleAPI private {

  import SimpleAPI._
  
  def shutDown : Unit =
    proofActor ! ShutdownCommand
  
  def reset = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    
    storedStates.clear
    
    currentOrder = TermOrder.EMPTY
    functionEnc =
      new FunctionEncoder(Param.TIGHT_FUNCTION_SCOPES(preprocSettings), false)
    currentProver = ModelSearchProver emptyIncProver goalSettings
    currentModel = null
  }
    
  //////////////////////////////////////////////////////////////////////////////
  //
  // Working with the vocabulary
  
  def createConstant(name : String) : ITerm = {
    val c = new ConstantTerm(name)
    currentOrder = currentOrder.extend(c, Set())
    c
  }
  
  def createConstant : ITerm =
    createConstant("c" + currentOrder.orderedConstants.size)
  
  def createBooleanVariable(name : String) : IFormula = {
    import IExpression._
    val p = new Predicate(name, 0)
    currentOrder = currentOrder extend p
    p()
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def !!(assertion : IFormula) : Unit = addAssertion(assertion)

  def addAssertion(assertion : IFormula) : Unit = {
    val sig =
      new Signature(Set(), Set(), currentOrder.orderedConstants, currentOrder)
    
    val (fors, _, newSig) =
      Preprocessing(!assertion, List(), sig, preprocSettings, functionEnc)
    functionEnc.clearAxioms
    currentOrder = newSig.order

    val completeFor =
      List(ReduceWithConjunction(Conjunction.TRUE, functionalPreds, currentOrder)(
          Conjunction.conj(InputAbsy2Internal(
            IExpression.connect(for (f <- fors.iterator)
                                  yield (IExpression removePartName f),
                                IBinJunctor.Or), currentOrder), currentOrder)))
    
    currentProver = currentProver.conclude(completeFor, currentOrder)
  }
  
  def ?? = checkSat(true)
  
  def checkSat(block : Boolean) : ProverStatus.Value = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    
    lastStatus = ProverStatus.Running
    proverRes.unset
    proofActor ! CheckSatCommand(currentProver)
    
    if (block)
      getStatus(true)
    else
      ProverStatus.Running
  }

  def getStatus(block : Boolean) : ProverStatus.Value =
    if (lastStatus != ProverStatus.Running || (!block && !proverRes.isSet)) {
      lastStatus
    } else {
      proverRes.get match {
        case UnsatResult =>
          lastStatus = ProverStatus.Unsat
        case SatResult(m) => {
          currentModel = m
   //       println(m)
          lastStatus = ProverStatus.Sat
        }
        case StoppedResult =>
          lastStatus = ProverStatus.Unknown
        case _ =>
          lastStatus = ProverStatus.Error
      }

      lastStatus
    }
  
  def stop : ProverStatus.Value = getStatus(false) match {
    case ProverStatus.Running => {
      proofActor ! StopCommand
      getStatus(true)
    }
    case res =>
      res
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def push : Unit =
    storedStates push (currentProver, currentOrder, functionEnc.clone)
  
  def pop : Unit = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    val (oldProver, oldOrder, oldFunctionEnc) = storedStates.pop
    currentProver = oldProver
    currentOrder = oldOrder
    functionEnc = oldFunctionEnc
  }
  
  def scope[A](comp: => A) = {
    push
    try {
      comp
    } finally {
      pop
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val preprocSettings = PreprocessingSettings.DEFAULT
  private val goalSettings = GoalSettings.DEFAULT

  private var currentOrder : TermOrder = _
  private var functionEnc : FunctionEncoder = _
  private var currentProver : ModelSearchProver.IncProver = _
  private var currentModel : Conjunction = _

  private val storedStates = new ArrayStack[(ModelSearchProver.IncProver,
                                             TermOrder,
                                             FunctionEncoder)]
  
  private def functionalPreds = functionEnc.predTranslation.keySet.toSet
  
  reset
  
  //////////////////////////////////////////////////////////////////////////////
  //
  // Prover actor, for the hard work
  
  private val proverRes = new SyncVar[ProverResult]
  private var lastStatus = ProverStatus.Unknown
  
  private val proofActor = actor {
    var cont = true
    
    Timeout.withChecker(() => receiveWithin(0) {
      case StopCommand =>
        Timeout.raise
      case ShutdownCommand => {
        cont = false
        Timeout.raise
      }
      case TIMEOUT => // nothing
    }) {
            
      while (cont) {
        receive {
          case CheckSatCommand(p) =>
          
            Timeout.catchTimeout {
              p checkValidity true
            } { case _ => null } match {
              
              case null => proverRes set StoppedResult
              case Left(m) if (!m.isFalse) => proverRes set SatResult(m)
              case _ => proverRes set UnsatResult
              
            }
          case ShutdownCommand =>
            cont = false
        }
      }
      
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  //
  // Theory of arrays
  
  private val selectFuns, storeFuns = new MHashMap[Int, IFunction]

}