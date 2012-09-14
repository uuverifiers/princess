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
import ap.terfor.TermOrder
import ap.terfor.TerForConvenience
import ap.proof.{ModelSearchProver, ExhaustiveProver}
import ap.terfor.equations.ReduceWithEqs
import ap.terfor.preds.{Atom, PredConj, ReduceWithPredLits}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               IterativeClauseMatcher, Quantifier}
import ap.util.{Debug, Timeout}

import scala.collection.mutable.{HashMap => MHashMap, ArrayStack}
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.concurrent.SyncVar

object SimpleAPI {
  
  private val AC = Debug.AC_SIMPLE_API

  def apply(enableAssert : Boolean = false,
            dumpSMT : Boolean = false) : SimpleAPI =
    new SimpleAPI (enableAssert, dumpSMT)

  def spawn : SimpleAPI = apply()
  def spawnWithAssertions : SimpleAPI = apply(enableAssert = true)
  def spawnWithLog : SimpleAPI = apply(dumpSMT = true)
  
  object ProverStatus extends Enumeration {
    val Sat, Unsat, Invalid, Valid, Unknown, Running, Error = Value
  }
  
  private abstract class ProverCommand

  private case class CheckSatCommand(prover : ModelSearchProver.IncProver)
          extends ProverCommand
  private case class CheckValidityCommand(formula : Conjunction,
                                          goalSettings : GoalSettings)
          extends ProverCommand
  private case object NextModelCommand extends ProverCommand
  private case object ShutdownCommand extends ProverCommand
  private case object StopCommand extends ProverCommand

  private abstract class ProverResult
  private case object UnsatResult extends ProverResult
  private case object InvalidResult extends ProverResult
  private case class SatResult(model : Conjunction) extends ProverResult
  private case object StoppedResult extends ProverResult

  private val badStringChar = """[^a-zA-Z_0-9']""".r
  
  private def sanitise(s : String) : String =
    badStringChar.replaceAllIn(s, (m : scala.util.matching.Regex.Match) =>
                                       ('a' + (m.toString()(0) % 26)).toChar.toString)

}

/**
 * API that simplifies the use of the prover; this tries to collect various
 * functionality in one place, and provides an imperative API similar to the
 * SMT-LIB command language.
 */
class SimpleAPI private (enableAssert : Boolean, dumpSMT : Boolean) {

  import SimpleAPI._
  
  private val dumpSMTStream = if (dumpSMT) {
    val dumpSMTFile = java.io.File.createTempFile("smt-queries-", ".smt2")
    new java.io.FileOutputStream(dumpSMTFile)
  } else {
    null
  }
  
  private def doDumpSMT(comp : => Unit) =
    if (dumpSMT) Console.withOut(dumpSMTStream) {
      comp
    }
  
  def shutDown : Unit = {
    proofActor ! ShutdownCommand
    doDumpSMT {
      println("(exit)")
    }
  }
  
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
    
    doDumpSMT {
      println("(reset)")
      println("(set-logic AUFLIA)")
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Working with the vocabulary
  
  def createConstant(rawName : String) : ITerm = {
    import IExpression._
    
    val name = sanitise(rawName)
    val c = new ConstantTerm(name)
    currentOrder = currentOrder extend c
    doDumpSMT {
      println("(declare-fun " + name + " () Int)")
    }
    c
  }

  def createConstant : ITerm =
    createConstant("c" + currentOrder.orderedConstants.size)
  
  def createConstants(num : Int) : IndexedSeq[ITerm] = {
    import IExpression._
    val startInd = currentOrder.orderedConstants.size
    val cs = (for (i <- 0 until num)
              yield {
                doDumpSMT {
                  println("(declare-fun " + ("c" + (startInd + i)) + " () Int)")
                }
                new ConstantTerm ("c" + (startInd + i))
              }).toIndexedSeq
    currentOrder = currentOrder extend cs
    for (c <- cs) yield IConstant(c)
  }

  def createBooleanVariable(rawName : String) : IFormula = {
    import IExpression._
    
    val name = sanitise(rawName)
    val p = new Predicate(name, 0)
    currentOrder = currentOrder extendPred p
    doDumpSMT {
      println("(declare-fun " + name + " () Bool)")
    }
    p()
  }

  def createBooleanVariable : IFormula =
    createBooleanVariable("p" + currentOrder.orderedPredicates.size)

  def createBooleanVariables(num : Int) : IndexedSeq[IFormula] = {
    import IExpression._
    val startInd = currentOrder.orderedPredicates.size
    val ps = (for (i <- 0 until num)
              yield {
                doDumpSMT {
                  println("(declare-fun " + ("p" + (startInd + i)) + " () Bool)")
                }
                new Predicate ("p" + (startInd + i), 0)
              }).toIndexedSeq
    currentOrder = currentOrder extendPred ps
    for (p <- ps) yield p()
  }

  def createFunction(rawName : String, arity : Int) : IFunction = {
    val name = sanitise(rawName)
    val f = new IFunction(name, arity, true, false)
    // make sure that the function encoder knows about the function
    val (_, newOrder) =
      functionEnc.apply(IFunApp(f, List.fill(arity)(0)) === 0, currentOrder)
    doDumpSMT {
      println("(declare-fun " + name + " (" +
          (for (_ <- 0 until arity) yield "Int").mkString(" ") + ") Int)")
    }
    currentOrder = newOrder
    recreateProver
    f
  }
  
  def createRelation(rawName : String, arity : Int) = {
    import IExpression._
    
    val name = sanitise(rawName)
    val r = new Predicate(name, arity)
    currentOrder = currentOrder extendPred r
    doDumpSMT {
      println("(declare-fun " + name + " (" +
          (for (_ <- 0 until arity) yield "Int").mkString(" ") + ") Bool)")
    }
    r
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

    doDumpSMT {
      println("(check-sat)")
    }

    lastStatus = ProverStatus.Running
    proverRes.unset
    
    flushTodo
    
    if (currentProver == null) {
      val completeFor = formulaeInProver match {
        case List(f) => f
        case formulae => 
          ReduceWithConjunction(Conjunction.TRUE, functionalPreds, currentOrder)(
            Conjunction.disj(formulae, currentOrder))
      }

      proofActor ! CheckValidityCommand(completeFor, goalSettings)
    } else {
      // use a ModelCheckProver
      proofActor ! CheckSatCommand(currentProver)
    }
    getStatus(block)
  }
  
  /**
   * After a <code>Sat</code> result, continue searching for the next model.
   * In most ways, this method behaves exactly like <code>checkSat</code>.
   */
  def nextModel(block : Boolean) : ProverStatus.Value = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) == ProverStatus.Sat)
    ////////////////////////////////////////////////////////////////////////////

    doDumpSMT {
      println("; (next-model)")
    }

    lastStatus = ProverStatus.Running
    proverRes.unset
    
    proofActor ! NextModelCommand
    getStatus(block)
  }

  /**
   * Query result of the last <code>checkSat</code> or <code>nextModel</code>
   * call. Will block until a result is available if <code>block</code>
   * argument is true, otherwise return immediately.
   */
  def getStatus(block : Boolean) : ProverStatus.Value = {
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
        case InvalidResult =>
          lastStatus = if (validityMode) ProverStatus.Invalid else ProverStatus.Sat
        case StoppedResult =>
          lastStatus = ProverStatus.Unknown
        case _ =>
          lastStatus = ProverStatus.Error
      }

      lastStatus
    }
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
    
    val c = new IExpression.ConstantTerm("c")
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
    
    doDumpSMT {
      println("; (get-value ...)")
    }
    
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
        
        val c = new IExpression.ConstantTerm ("c")
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
    
    val p = new IExpression.Predicate("p", 0)
    implicit val extendedOrder = currentOrder extendPred p
    val extendedProver =
      currentProver.conclude(currentModel, extendedOrder)
                   .conclude(toInternal(IAtom(p, Seq()) </> f, extendedOrder),
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
    import TerForConvenience._
    
    doDumpSMT {
      print("(get-value (")
      SMTLineariser(f)
      println("))")
    }
    
    f match {
      case IAtom(p, args) if (args forall (_.isInstanceOf[IIntLit])) => {
        val a = Atom(p, for (IIntLit(value) <- args) yield l(value), currentOrder)
        
        if (currentModel.predConj.positiveLitsAsSet contains a)
          Some(true)
        else if (currentModel.predConj.negativeLitsAsSet contains a)
          Some(false)
        else
          None
      }
      case _ => {
        // more complex check by reducing the expression via the model
        
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
    }
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
    
    doDumpSMT {
      println("(push 1)")
    }
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
    
    doDumpSMT {
      println("(pop 1)")
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def flushTodo : Unit = formulaeTodo match {
    case IBoolLit(false) => // nothing
    case f => {
      val completeFor = toInternal(f, currentOrder)
      formulaeInProver = completeFor :: formulaeInProver

      if (currentProver != null) {
        if (IterativeClauseMatcher isMatchableRec completeFor)
          currentProver = currentProver.conclude(completeFor, currentOrder)
        else
          currentProver = null
      }
      formulaeTodo = false
    }
  }
  
  private def addFormula(f : IFormula) : Unit = {
    currentModel = null
    lastStatus = ProverStatus.Unknown
    doDumpSMT {
      print("(assert (not ")
      SMTLineariser(f)
      println("))")
    }
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
    var nextCommand : ProverCommand = null
    
    val commandParser : PartialFunction[Any, Unit] = {
      case CheckSatCommand(p) =>
          
        Timeout.catchTimeout {
          p.checkValidity(true, (model : Conjunction) => {
            ////////////////////////////////////////////////////////////////////
            Debug.assertPre(AC, !model.isFalse)
            ////////////////////////////////////////////////////////////////////
            proverRes set SatResult(model)
                
            // wait for a command on what to do next
            receive {
              case NextModelCommand => {
                false
              }
              case c : ProverCommand => {
                // get out of here
                nextCommand = c
                true
              }
            }
          })
        } { case _ => null } match {

          case null =>
            proverRes set StoppedResult
          case Left(m) if (nextCommand == null) =>
            proverRes set UnsatResult
          case Left(_) =>
            // nothing
              
        }

      case CheckValidityCommand(formula, goalSettings) =>
        
        Timeout.catchTimeout {
          
          // explicitly quantify all universal variables
          val closedFor = Conjunction.quantify(Quantifier.ALL,
                                               formula.order sort formula.constants,
                                               formula, formula.order)

          (new ExhaustiveProver (true, goalSettings))(closedFor, formula.order)
          
        } { case _ => null } match {
          
          case null =>
            proverRes set StoppedResult
          case tree =>
            if (tree.closingConstraint.isTrue)
              proverRes set UnsatResult
            else
              proverRes set InvalidResult
            
        }
        
      case StopCommand =>
        proverRes set StoppedResult
      case ShutdownCommand =>
        cont = false
    }
    
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
        // wait for a command on what to do next
        if (nextCommand != null) {
          val c = nextCommand
          nextCommand = null
          commandParser(c)
        } else {
          receive(commandParser)
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