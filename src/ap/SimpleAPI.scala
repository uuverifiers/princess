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

import ap.basetypes.IdealInt
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.TerForConvenience
import ap.proof.ModelSearchProver
import ap.terfor.equations.ReduceWithEqs
import ap.terfor.preds.{Predicate, Atom, PredConj, ReduceWithPredLits}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.util.{Debug, Timeout}

import scala.collection.mutable.{HashMap => MHashMap, SynchronizedQueue,
                                 ArrayStack}
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.concurrent.SyncVar

object SimpleAPI {
  
  private val AC = Debug.AC_SIMPLE_API

  def spawn : SimpleAPI = new SimpleAPI (false)
  def spawnWithAssertions : SimpleAPI = new SimpleAPI (true)
  
  object ProverStatus extends Enumeration {
    val Sat, Unsat, Invalid, Valid, Unknown, Running, Error = Value
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
class SimpleAPI private (enableAssert : Boolean) {

  import SimpleAPI._
  
  def shutDown : Unit =
    proofActor ! ShutdownCommand
  
  def reset = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    
    storedStates.clear
    
    preprocSettings = PreprocessingSettings.DEFAULT
    currentOrder = TermOrder.EMPTY
    functionEnc =
      new FunctionEncoder(Param.TIGHT_FUNCTION_SCOPES(preprocSettings), false)
    currentProver = ModelSearchProver emptyIncProver goalSettings
    formulaeInProver = List()
    formulaeTodo = false
    currentModel = null
    lastStatus = ProverStatus.Sat
    validityMode = false
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Working with the vocabulary
  
  def createConstant(name : String) : ITerm = {
    val c = new ConstantTerm(name)
    currentOrder = currentOrder extend c
    c
  }

  def createConstant : ITerm =
    createConstant("c" + currentOrder.orderedConstants.size)
  
  def createConstants(num : Int) : IndexedSeq[ITerm] = {
    val startInd = currentOrder.orderedConstants.size
    val cs = (for (i <- 0 until num)
              yield new ConstantTerm ("c" + (startInd + i))).toIndexedSeq
    currentOrder = currentOrder extend cs
    for (c <- cs) yield IConstant(c)
  }

  def createBooleanVariable(name : String) : IFormula = {
    import IExpression._
    val p = new Predicate(name, 0)
    currentOrder = currentOrder extendPred p
    p()
  }

  def createBooleanVariable : IFormula =
    createBooleanVariable("p" + currentOrder.orderedPredicates.size)

  def createBooleanVariables(num : Int) : IndexedSeq[IFormula] = {
    import IExpression._
    val startInd = currentOrder.orderedPredicates.size
    val ps = (for (i <- 0 until num)
              yield new Predicate ("p" + (startInd + i), 0)).toIndexedSeq
    currentOrder = currentOrder extendPred ps
    for (p <- ps) yield p()
  }

  def createFunction(name : String, arity : Int) : IFunction = {
    val f = new IFunction(name, arity, true, false)
    // make sure that the function encoder knows about the function
    val (_, newOrder) =
      functionEnc.apply(IFunApp(f, List.fill(arity)(0)) === 0, currentOrder)
    currentOrder = newOrder
    recreateProver
    f
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def selectFun(arity : Int) : IFunction = getArrayFuns(arity)._1
  
  def storeFun(arity : Int) : IFunction = getArrayFuns(arity)._2
  
  def select(args : ITerm*) : ITerm = IFunApp(selectFun(args.size - 1), args)

  def store(args : ITerm*) : ITerm = IFunApp(storeFun(args.size - 2), args)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an assertion to the prover: assume that the given formula is true
   */
  def !!(assertion : IFormula) : Unit =
    addAssertion(assertion)

  def addAssertion(assertion : IFormula) : Unit =
    addFormula(!assertion)
  
  /**
   * Add a conclusion to the prover: assume that the given formula is false.
   * Adding conclusions will switch the prover to "validity" mode; from this
   * point on, the prover answers with the status <code>Valid/Invalid</code>
   * instead of <code>Unsat/Sat</code>.
   */
  def ??(conc : IFormula) : Unit =
    addConclusion(conc)

  def addConclusion(conc : IFormula) : Unit = {
    validityMode = true
    addFormula(conc)
  }
  
  /**
   * Determine the status of the formulae asserted up to this point. This
   * call is blocking, but will not run the prover repeatedly if nothing
   * has changed since the last check.
   */
  def ??? = getStatus(true) match {
    case ProverStatus.Unknown => checkSat(true)
    case res => res
  }
  
  /**
   * Check satisfiability of the currently asserted formulae. Will block until
   * completion if <code>block</code> argument is true, otherwise return
   * immediately.
   */
  def checkSat(block : Boolean) : ProverStatus.Value = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    
    lastStatus = ProverStatus.Running
    proverRes.unset
    
    flushTodo
    
    proofActor ! CheckSatCommand(currentProver)
    
    if (block)
      getStatus(true)
    else
      ProverStatus.Running
  }

  /**
   * Query result of the last <code>checkSat</code> or <code>nextModel</code>
   * call. Will block until a result is available if <code>block</code>
   * argument is true, otherwise return immediately.
   */
  def getStatus(block : Boolean) : ProverStatus.Value =
    if (lastStatus != ProverStatus.Running || (!block && !proverRes.isSet)) {
      lastStatus
    } else {
      proverRes.get match {
        case UnsatResult =>
          lastStatus = if (validityMode) ProverStatus.Valid else ProverStatus.Unsat
        case SatResult(m) => {
          currentModel = m
//          println(m)
          lastStatus = if (validityMode) ProverStatus.Invalid else ProverStatus.Sat
        }
        case StoppedResult =>
          lastStatus = ProverStatus.Unknown
        case _ =>
          lastStatus = ProverStatus.Error
      }

      lastStatus
    }
  
  /**
   * Stop a running prover. If the prover had already terminated, give same
   * result as <code>getResult</code>, otherwise <code>Unknown</code>.
   */
  def stop : ProverStatus.Value = getStatus(false) match {
    case ProverStatus.Running => {
      proofActor ! StopCommand
      getStatus(true)
    }
    case res =>
      res
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def eval(t : ITerm) : IdealInt = evalPartial(t) getOrElse {
    // then we have to extend the model
    
    import TerForConvenience._
    
    val c = new ConstantTerm("c")
    implicit val extendedOrder = currentOrder.extend(c)
    val extendedProver =
      currentProver.conclude(currentModel, extendedOrder)
                   .conclude(toInternal(IExpression.i(c) =/= t, extendedOrder),
                             extendedOrder)
    
    (extendedProver checkValidity true) match {
      case Left(m) if (!m.isFalse) => {
        val reduced = ReduceWithEqs(m.arithConj.positiveEqs, extendedOrder)(l(c))
        //////////////////////////////////////////////////////////////////////
        Debug.assertInt(AC, reduced.constants.isEmpty)
        //////////////////////////////////////////////////////////////////////
        val result = reduced.constant
        currentModel = ConstantSubst(c, result, extendedOrder)(m)
        
        result
      }
    }
  }
  
  def evalPartial(t : ITerm) : Option[IdealInt] = {
    import TerForConvenience._
    
    t match {
      case IConstant(c) => {
        // faster check, find an equation that determines the value of c
        
        implicit val o = currentOrder
        
        val eqs = currentModel.arithConj.positiveEqs
        if (eqs.constants contains c) {
          val reduced = ReduceWithEqs(eqs, currentOrder)(l(c))
          //////////////////////////////////////////////////////////////////////
          Debug.assertInt(AC, reduced.constants.isEmpty)
          //////////////////////////////////////////////////////////////////////
          Some(reduced.constant)
        } else
          None
      }
      
      case t => {
        // more complex check by reducing the expression via the model
        
        val c = new ConstantTerm ("c")
        val extendedOrder = currentOrder.extend(c)
        
        val reduced = ReduceWithConjunction(currentModel, functionalPreds,
                                            extendedOrder)(
                                            toInternal(t === c, extendedOrder))
        if (reduced.isLiteral &&
            reduced.arithConj.positiveEqs.size == 1 &&
            reduced.constants.size == 1)
          Some(-reduced.arithConj.positiveEqs.head.constant)
        else
          None
      }
    }
  }

  def eval(f : IFormula) : Boolean = evalPartial(f) getOrElse {
    // then we have to extend the model

    import TerForConvenience._
    
    val p = new Predicate("p", 0)
    implicit val extendedOrder = currentOrder extendPred p
    val extendedProver =
      currentProver.conclude(currentModel, extendedOrder)
                   .conclude(toInternal(IAtom(p, Seq()) <=> f, extendedOrder),
                             extendedOrder)
    
    (extendedProver checkValidity true) match {
      case Left(m) if (!m.isFalse) => {
        val (reduced, _) = ReduceWithPredLits(m.predConj, Set(), extendedOrder)(p)
        //////////////////////////////////////////////////////////////////////
        Debug.assertInt(AC, reduced.isTrue || reduced.isFalse)
        //////////////////////////////////////////////////////////////////////
        val result = reduced.isTrue
        val pf : Conjunction = p
        
        currentModel = ReduceWithConjunction(if (result) pf else !pf, extendedOrder)(m)
        
        result
      }
    }
  }

  def evalPartial(f : IFormula) : Option[Boolean] = {
    val reduced =
      ReduceWithConjunction(currentModel, functionalPreds, currentOrder)(
                              toInternal(f, currentOrder))
    
    if (reduced.isTrue)
      Some(true)
    else if (reduced.isFalse)
      Some(false)
    else
      None
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Execute a computation within a local scope. After leaving the scope,
   * assertions and declarations done in the meantime will disappear.
   */
  def scope[A](comp: => A) = {
    push
    try {
      comp
    } finally {
      pop
    }
  }
  
  /**
   * Add a new frame to the assertion stack.
   */
  def push : Unit = {
    // process pending formulae, to avoid processing them again after a pop
    flushTodo
    
    storedStates push (preprocSettings,
                       currentProver, currentOrder, functionEnc.clone,
                       arrayFuns, formulaeInProver, validityMode,
                       lastStatus, currentModel)
  }
  
  /**
   * Pop the top-most frame from the assertion stack.
   */
  def pop : Unit = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    ////////////////////////////////////////////////////////////////////////////
    val (oldPreprocSettings, oldProver, oldOrder, oldFunctionEnc, oldArrayFuns,
         oldFormulaeInProver, oldValidityMode, oldStatus, oldModel) =
      storedStates.pop
    preprocSettings = oldPreprocSettings
    currentProver = oldProver
    currentOrder = oldOrder
    functionEnc = oldFunctionEnc
    arrayFuns = oldArrayFuns
    formulaeInProver = oldFormulaeInProver
    formulaeTodo = false
    validityMode = oldValidityMode
    lastStatus = oldStatus
    currentModel = oldModel
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def flushTodo : Unit = formulaeTodo match {
    case IBoolLit(false) => // nothing
    case f => {
      val completeFor = toInternal(f, currentOrder)
      formulaeInProver = completeFor :: formulaeInProver
      currentProver = currentProver.conclude(completeFor, currentOrder)
      formulaeTodo = false
    }
  }
  
  private def addFormula(f : IFormula) : Unit = {
    currentModel = null
    lastStatus = ProverStatus.Unknown
    formulaeTodo = formulaeTodo | f
  }

  private def toInternal(f : IFormula, order : TermOrder) : Conjunction = {
    val sig = new Signature(Set(), Set(), order.orderedConstants, order)
    val (fors, _, newSig) = Preprocessing(f, List(), sig, preprocSettings, functionEnc)
    functionEnc.clearAxioms
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, order == newSig.order)
    ////////////////////////////////////////////////////////////////////////////

    ReduceWithConjunction(Conjunction.TRUE, functionalPreds, order)(
      Conjunction.conj(InputAbsy2Internal(
        IExpression.connect(for (f <- fors.iterator)
                              yield (IExpression removePartName f),
                            IBinJunctor.Or), order), order))
  }
  
  private var preprocSettings : PreprocessingSettings = _
  private def goalSettings = {
    var gs = GoalSettings.DEFAULT
//    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
//    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
//    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs,
        (for ((p, f) <- functionEnc.predTranslation.iterator; if (!f.partial))
         yield p).toSet)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs
  }

  private var currentOrder : TermOrder = _
  private var functionEnc : FunctionEncoder = _
  private var currentProver : ModelSearchProver.IncProver = _
  private var currentModel : Conjunction = _
  private var formulaeInProver : List[Conjunction] = List()
  private var formulaeTodo : IFormula = false
  
  private val storedStates = new ArrayStack[(PreprocessingSettings,
                                             ModelSearchProver.IncProver,
                                             TermOrder,
                                             FunctionEncoder,
                                             Map[Int, (IFunction, IFunction)],
                                             List[Conjunction],
                                             Boolean,
                                             ProverStatus.Value,
                                             Conjunction)]
  
  private def recreateProver = {
    preprocSettings = {
      var ps = PreprocessingSettings.DEFAULT
      ps = Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
             ps, functionEnc.predTranslation.values.toSet)
      ps
    }
    currentProver = (ModelSearchProver emptyIncProver goalSettings)
                        .conclude(formulaeInProver, currentOrder)
  }
  
  private def functionalPreds = functionEnc.predTranslation.keySet.toSet
  
  //////////////////////////////////////////////////////////////////////////////
  //
  // Prover actor, for the hard work
  
  private val proverRes = new SyncVar[ProverResult]
  private var lastStatus : ProverStatus.Value = _
  private var validityMode : Boolean = _
  
  private val proofActor = actor {
    Debug enableAllAssertions enableAssert
    
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

  private var arrayFuns : Map[Int, (IFunction, IFunction)] = Map()
  
  private def getArrayFuns(arity : Int) : (IFunction, IFunction) =
    arrayFuns.getOrElse(arity, {
      val select = createFunction("select" + arity, arity + 1)
      val store = createFunction("store" + arity, arity + 2)
      arrayFuns += (arity -> (select, store))
      addFormula(!Parser2InputAbsy.arrayAxioms(arity, select, store))
      (select, store)
    })
  
  //////////////////////////////////////////////////////////////////////////////

  reset

}