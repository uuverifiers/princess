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
import ap.terfor.{TermOrder, Formula}
import ap.terfor.TerForConvenience
import ap.proof.{ModelSearchProver, ExhaustiveProver}
import ap.proof.certificates.Certificate
import ap.interpolants.{ProofSimplifier, InterpolationContext, Interpolator,
                        InterpolantSimplifier}
import ap.terfor.equations.ReduceWithEqs
import ap.terfor.preds.{Atom, PredConj, ReduceWithPredLits}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               IterativeClauseMatcher, Quantifier}
import ap.util.{Debug, Timeout, Seqs}

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
  
  private object ProofActorStatus extends Enumeration {
    val Init, AtPartialModel, AtFullModel = Value
  }
  
  private abstract class ProverCommand

  private case class CheckSatCommand(prover : ModelSearchProver.IncProver)
          extends ProverCommand
  private case class CheckValidityCommand(formula : Conjunction,
                                          goalSettings : GoalSettings,
                                          mostGeneralConstraint : Boolean)
          extends ProverCommand
  private case object NextModelCommand extends ProverCommand
  private case class  AddFormulaCommand(formula : Conjunction) extends ProverCommand
  private case object RecheckCommand extends ProverCommand
  private case object DeriveFullModelCommand extends ProverCommand
  private case object ShutdownCommand extends ProverCommand
  private case object StopCommand extends ProverCommand

  private abstract class ProverResult
  private case object UnsatResult extends ProverResult
  private case class  FoundConstraintResult(constraint : Conjunction,
                                            model : Conjunction)
                                           extends ProverResult
  private case class  UnsatCertResult(cert : Certificate) extends ProverResult
  private case object InvalidResult extends ProverResult
  private case class SatResult(model : Conjunction) extends ProverResult
  private case class SatPartialResult(model : Conjunction) extends ProverResult
  private case object StoppedResult extends ProverResult

  private val badStringChar = """[^a-zA-Z_0-9']""".r
  
  private def sanitise(s : String) : String =
    badStringChar.replaceAllIn(s, (m : scala.util.matching.Regex.Match) =>
                                       ('a' + (m.toString()(0) % 26)).toChar.toString)

  private val FormulaPart = new PartName ("formula")
}

/**
 * API that simplifies the use of the prover; this tries to collect various
 * functionality in one place, and provides an imperative API similar to the
 * SMT-LIB command language.
 */
class SimpleAPI private (enableAssert : Boolean, dumpSMT : Boolean) {

  import SimpleAPI._

  Debug enableAllAssertions enableAssert

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
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    storedStates.clear
    
    preprocSettings = PreprocessingSettings.DEFAULT
    currentOrder = TermOrder.EMPTY
    existentialConstants = Set()
    functionEnc =
      new FunctionEncoder(Param.TIGHT_FUNCTION_SCOPES(preprocSettings), false)
    currentProver = ModelSearchProver emptyIncProver goalSettings
    formulaeInProver = List()
    formulaeTodo = false
    currentModel = null
    currentConstraint = null
    currentCertificate = null
    lastStatus = ProverStatus.Sat
    validityMode = false
    proofActorStatus = ProofActorStatus.Init
    currentPartitionNum = -1
    constructProofs = false
    mostGeneralConstraints = false
    
    doDumpSMT {
      println("(reset)")
      println("(set-logic AUFLIA)")
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Working with the vocabulary
  
  /**
   * Create a new symbolic constant.
   */
  def createConstant(rawName : String) : ITerm = {
    import IExpression._
    createConstantRaw(rawName)
  }

  /**
   * Create a new symbolic constant with predefined name.
   */
  def createConstant : ITerm =
    createConstant("c" + currentOrder.orderedConstants.size)
  
  /**
   * Create <code>num</code> new symbolic constant with predefined name.
   */
  def createConstants(num : Int) : IndexedSeq[ITerm] = {
    val start = currentOrder.orderedConstants.size
    for (c <- createConstantsRaw("c", start until (start + num))) yield IConstant(c)
  }

  /**
   * Create a new symbolic constant, without directly turning it into an
   * <code>ITerm</code>. This method is
   * only useful when working with formulae in the internal prover format.
   */
  def createConstantRaw(rawName : String) : IExpression.ConstantTerm = {
    import IExpression._
    
    val name = sanitise(rawName)
    val c = new ConstantTerm(name)
    currentOrder = currentOrder extend c
    doDumpSMT {
      println("(declare-fun " + name + " () Int)")
    }
    c
  }

  /**
   * Create a sequence of new symbolic constants, without directly turning them into an
   * <code>ITerm</code>. This method is
   * only useful when working with formulae in the internal prover format.
   */
  def createConstantsRaw(prefix : String, nums : Range)
                        : IndexedSeq[IExpression.ConstantTerm] = {
    import IExpression._
    val cs = (for (i <- nums)
              yield {
                doDumpSMT {
                  println("(declare-fun " + (prefix + i) + " () Int)")
                }
                new ConstantTerm (prefix + i)
              }).toIndexedSeq
    currentOrder = currentOrder extend cs
    cs
  }

  /**
   * Create a new symbolic constant that is implicitly existentially quantified.
   */
  def createExistentialConstant(rawName : String) : ITerm = {
    import IExpression._
    val c = createConstantRaw(rawName)
    existentialConstants = existentialConstants + c
    c
  }
  
  /**
   * Create a new symbolic constant with predefined name that is implicitly
   * existentially quantified.
   */
  def createExistentialConstant : ITerm =
    createExistentialConstant("X" + currentOrder.orderedConstants.size)
  
 /**
   * Create <code>num</code> new symbolic constant with predefined name that is
   * implicitly existentially quantified.
   */
  def createExistentialConstants(num : Int) : IndexedSeq[ITerm] = {
    val start = currentOrder.orderedConstants.size
    val cs = createConstantsRaw("X", start until (start + num))
    existentialConstants = existentialConstants ++ cs
    for (c <- cs) yield IConstant(c)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an externally defined constant to the environment of this prover.
   */
  def addConstant(c : IExpression.ConstantTerm) : Unit = {
    currentOrder = currentOrder extend c
    doDumpSMT {
      println("(declare-fun " + c.name + " () Int)")
    }
  } 

  /**
   * Add a sequence of externally defined constant to the environment of
   * this prover.
   */
  def addConstants(cs : Iterable[IExpression.ConstantTerm]) : Unit = {
    currentOrder = currentOrder extend cs.toSeq
    doDumpSMT {
      for (c <- cs)
        println("(declare-fun " + c.name + " () Int)")
    }
  }

  /**
   * Create a new Boolean variable (nullary predicate).
   */
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

  /**
   * Create a new Boolean variable (nullary predicate) with predefined name.
   */
  def createBooleanVariable : IFormula =
    createBooleanVariable("p" + currentOrder.orderedPredicates.size)

  /**
   * Create <code>num</code> new Boolean variable (nullary predicate) with
   * predefined name.
   */
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

  /**
   * Create a new uninterpreted function with fixed arity.
   */
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
  
  /**
   * Create a new uninterpreted predicate with fixed arity.
   */
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
  
  /**
   * Export the current <code>TermOrder</code> of the prover. This method is
   * only useful when working with formulae in the internal prover format.
   */
  def order = currentOrder
  
  /**
   * Pretty-print a formula or term.
   */
  def pp(f : IExpression) : String =
    DialogUtil asString { PrincessLineariser printExpression f }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * <code>select</code> function of the theory of arrays.
   */
  def selectFun(arity : Int) : IFunction = getArrayFuns(arity)._1
  
  /**
   * <code>store</code> function of the theory of arrays.
   */
  def storeFun(arity : Int) : IFunction = getArrayFuns(arity)._2
  
  /**
   * Generate a <code>select</code> expression in the theory of arrays.
   */
  def select(args : ITerm*) : ITerm = IFunApp(selectFun(args.size - 1), args)

  /**
   * Generate a <code>store</code> expression in the theory of arrays.
   */
  def store(args : ITerm*) : ITerm = IFunApp(storeFun(args.size - 2), args)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an assertion to the prover: assume that the given formula is true
   */
  def !!(assertion : IFormula) : Unit =
    addAssertion(assertion)

  /**
   * Add an assertion to the prover: assume that the given formula is true
   */
  def addAssertion(assertion : IFormula) : Unit =
    addFormula(!assertion)
  
  /**
   * Add an assertion to the prover: assume that the given formula is true
   */
  def addAssertion(assertion : Formula) : Unit =
    addFormula(Conjunction.negate(assertion, currentOrder))
    
  /**
   * Add a conclusion to the prover: assume that the given formula is false.
   * Adding conclusions will switch the prover to "validity" mode; from this
   * point on, the prover answers with the status <code>Valid/Invalid</code>
   * instead of <code>Unsat/Sat</code>.
   */
  def ??(conc : IFormula) : Unit =
    addConclusion(conc)

  /**
   * Add a conclusion to the prover: assume that the given formula is false.
   * Adding conclusions will switch the prover to "validity" mode; from this
   * point on, the prover answers with the status <code>Valid/Invalid</code>
   * instead of <code>Unsat/Sat</code>.
   */
  def addConclusion(conc : IFormula) : Unit = {
    validityMode = true
    addFormula(conc)
  }
  
  /**
   * Add a conclusion to the prover: assume that the given formula is false.
   * Adding conclusions will switch the prover to "validity" mode; from this
   * point on, the prover answers with the status <code>Valid/Invalid</code>
   * instead of <code>Unsat/Sat</code>.
   */
  def addConclusion(conc : Formula) : Unit = {
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
    doDumpSMT {
      println("(check-sat)")
    }

    getStatus(false) match {
      case ProverStatus.Unknown => {
        lastStatus = ProverStatus.Running
        proverRes.unset
    
        flushTodo
    
        proofActorStatus match {
          case ProofActorStatus.Init =>
            if (currentProver == null) {
              val completeFor = formulaeInProver match {
                case List((_, f)) => f
                case formulae => 
                  ReduceWithConjunction(Conjunction.TRUE, functionalPreds, currentOrder)(
                    Conjunction.disj(for ((_, f) <- formulae.iterator) yield f,
                                     currentOrder))
              }

              // explicitly quantify all universal variables
              val uniConstants = completeFor.constants -- existentialConstants
              val closedFor = Conjunction.quantify(Quantifier.ALL,
                                                   currentOrder sort uniConstants,
                                                   completeFor, currentOrder)

              proofActor ! CheckValidityCommand(closedFor, goalSettings,
                                                mostGeneralConstraints)
            } else {
              // use a ModelCheckProver
              proofActor ! CheckSatCommand(currentProver)
            }
            
          case ProofActorStatus.AtPartialModel | ProofActorStatus.AtFullModel => {
            proofActorStatus = ProofActorStatus.Init
            proofActor ! RecheckCommand
          }
        }
        
        getStatus(block)
      }
      
      case ProverStatus.Running => {
        assert(false)
        ProverStatus.Error
      }
        
      case s => s
    }
  }
  
  /**
   * After a <code>Sat</code> result, continue searching for the next model.
   * In most ways, this method behaves exactly like <code>checkSat</code>.
   */
  def nextModel(block : Boolean) : ProverStatus.Value = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) == ProverStatus.Sat)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

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
        case UnsatResult => {
          currentModel = Conjunction.TRUE
          currentConstraint = Conjunction.TRUE
          lastStatus =
            if (validityMode) ProverStatus.Valid else ProverStatus.Unsat
        }
        case UnsatCertResult(cert) => {
          currentModel = Conjunction.TRUE
          currentConstraint = Conjunction.TRUE
          currentCertificate = ProofSimplifier(cert)
          lastStatus =
            if (validityMode) ProverStatus.Valid else ProverStatus.Unsat
        }
        case FoundConstraintResult(constraint, m) => {
          currentModel = m
          currentConstraint = constraint
          lastStatus =
            if (validityMode) ProverStatus.Valid else ProverStatus.Unsat
        }
        case SatResult(m) => {
          currentModel = m
          lastStatus =
            if (validityMode) ProverStatus.Invalid else ProverStatus.Sat
          proofActorStatus = ProofActorStatus.AtFullModel
        }
        case SatPartialResult(m) => {
          currentModel = m
          lastStatus =
            if (validityMode) ProverStatus.Invalid else ProverStatus.Sat
          proofActorStatus = ProofActorStatus.AtPartialModel
        }
        case InvalidResult =>
          // no model is available in this case
          lastStatus =
            if (validityMode) ProverStatus.Invalid else ProverStatus.Sat
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

  /**
   * Add subsequent formulae to partition <code>num</code>.
   *  Index <code>-1</code> represents
   * formulae belonging to all partitions (e.g., theory axioms).
   */
  def setPartitionNumber(num : Int) : Unit = if (currentPartitionNum != num) {
    flushTodo
    currentPartitionNum = num
  }
  
  /**
   * Construct proofs in subsequent <code>checkSat</code> calls. Proofs are
   * needed for extract interpolants.
   */
  def setConstructProofs(b : Boolean) : Unit = if (constructProofs != b) {
    constructProofs = b
    recreateProver
  }

  /**
   * Compute an inductive sequence of interpolants, for the given
   * partitioning of the input problem.
   */
  def getInterpolants(partitions : Seq[Set[Int]]) : Seq[IFormula] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (Set(ProverStatus.Unsat,
                             ProverStatus.Valid) contains getStatus(false)) &&
                        currentCertificate != null)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  
    doDumpSMT {
      println("; (get-interpolants)")
    }

    val simp = interpolantSimplifier
                        
    for (i <- 1 to (partitions.size - 1)) yield {
      val leftNums = (partitions take i).flatten.toSet
      
      val commonFors = for ((n, f) <- formulaeInProver;
                            if (n < 0)) yield f
      val leftFors =   for ((n, f) <- formulaeInProver;
                            if (n >= 0 && (leftNums contains n))) yield f
      val rightFors =  for ((n, f) <- formulaeInProver;
                            if (n >= 0 && !(leftNums contains n))) yield f

      val iContext =
        InterpolationContext(leftFors, rightFors, commonFors, currentOrder)
      val internalInt = Interpolator(currentCertificate, iContext)

      val interpolant = Internal2InputAbsy(internalInt, functionEnc.predTranslation)

      simp(interpolant)
    }
  }
  
  private def interpolantSimplifier = (arrayFuns get 1) match {
    case None => new Simplifier
    case Some((sel, sto)) => new InterpolantSimplifier(sel, sto)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * In subsequent <code>checkSat</code> calls for problems with existential
   * constants, infer the most general constraint on existential constants
   * satisfying the problem. NB: If this option is used wrongly, it might
   * lead to non-termination of the prover.
   */
  def setMostGeneralConstraints(b : Boolean) : Unit =
    mostGeneralConstraints = b
  
  /**
   * After receiving the result
   * <code>ProverStatus.Unsat</code> or <code>ProverStates.Valid</code>
   * for a problem that contains existential constants, return a (satisfiable)
   * constraint over the existential constants that describes satisfying
   * assignments of the existential constants.
   */
  def getConstraint : IFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, Set(ProverStatus.Unsat,
                            ProverStatus.Valid) contains getStatus(false))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    (new Simplifier)(Internal2InputAbsy(currentConstraint, Map()))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def ensureFullModel =
    while (proofActorStatus == ProofActorStatus.AtPartialModel) {
      // let's get a complete model first
      lastStatus = ProverStatus.Running
      proverRes.unset
      proofActor ! DeriveFullModelCommand
      getStatus(true)
    }
  
  /**
   * Evaluate the given term in the current model. This method can be
   * called in two situations:
   * <ul>
   *    <li> after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>, in
   * which case the term is evaluated in the computed model, or</li>
   * <li> after receiving
   * the result
   * <code>ProverStatus.Unsat</code> or <code>ProverStates.Valid</code>
   * for a problem that contains existential constants. In this case the
   * queried term <code>t</code> may only consist of existential constants.
   * </li>
   * </ul>
   */
  def eval(t : ITerm) : IdealInt = evalPartial(t) getOrElse {
    // then we have to extend the model
    
    import TerForConvenience._
    
    val c = new IExpression.ConstantTerm("c")
    implicit val extendedOrder = currentOrder extend c
    val baseProver = getStatus(false) match {
      case ProverStatus.Sat | ProverStatus.Invalid if (currentModel != null) =>
        // then we work with a countermodel of the constraints
        currentProver
      
      case ProverStatus.Unsat | ProverStatus.Valid if (currentModel != null) =>
        // the we work with a model of the existential constants 
        ModelSearchProver emptyIncProver goalSettings
      
      case _ => {
        assert(false)
        null
      }
    }

    val extendedProver =
      baseProver.assert(currentModel, extendedOrder)
                .conclude(toInternal(IExpression.i(c) =/= t, extendedOrder)._1,
                          extendedOrder)
    
    (extendedProver checkValidity true) match {
      case Left(m) if (!m.isFalse) => {
        val reduced = ReduceWithEqs(m.arithConj.positiveEqs, extendedOrder)(l(c))
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, reduced.constants.isEmpty)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val result = reduced.constant
        currentModel = ConstantSubst(c, result, extendedOrder)(m)
        
        result
      }
    }
  }
  
  /**
   * Evaluate the given term in the current model, returning <code>None</code>
   * in case the model does not completely determine the value of the term.
   * This method can be
   * called in two situations:
   * <ul>
   *    <li> after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>, in
   * which case the term is evaluated in the computed model, or</li>
   * <li> after receiving
   * the result
   * <code>ProverStatus.Unsat</code> or <code>ProverStates.Valid</code>
   * for a problem that contains existential constants. In this case the
   * queried term <code>t</code> may only consist of existential constants.
   * </li>
   * </ul>
   */
  def evalPartial(t : ITerm) : Option[IdealInt] = {
    import TerForConvenience._

    val existential = getStatus(false) match {
      case ProverStatus.Sat | ProverStatus.Invalid if (currentModel != null) => {
        // then we work with a countermodel of the constraints
        doDumpSMT {
          println("; (get-value ...)")
        }
    
        ensureFullModel
        
        false
      }
      
      case ProverStatus.Unsat | ProverStatus.Valid if (currentModel != null) => {
        // the we work with a model of the existential constants 
        doDumpSMT {
          println("; (get-value for existential constants ...)")
        }
        
        true
      }
      
      case _ => {
        assert(false)
        false
      }
    }
    
    t match {
      case IConstant(c) => {
        // faster check, find an equation that determines the value of c
        
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, !existential || (existentialConstants contains c))
        //-END-ASSERTION-///////////////////////////////////////////////////////
          
        implicit val o = currentOrder
        
        val eqs = currentModel.arithConj.positiveEqs
        if (eqs.constants contains c) {
          val reduced = ReduceWithEqs(eqs, currentOrder)(l(c))
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, reduced.constants.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          Some(reduced.constant)
        } else
          None
      }
      
      case t => {
        // more complex check by reducing the expression via the model
        
        val c = new IExpression.ConstantTerm ("c")
        val extendedOrder = currentOrder extend c
        
        val reduced =
          ReduceWithConjunction(currentModel, functionalPreds, extendedOrder)(
                                toInternal(t === c, extendedOrder)._1)

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, !existential || (
          // in the existential case, the queried term should only contain
          // existential constants
          (reduced.constants subsetOf (existentialConstants + c)) &&
          reduced.predicates.isEmpty
          ))
        //-END-ASSERTION-///////////////////////////////////////////////////////
          
        if (reduced.isLiteral &&
            reduced.arithConj.positiveEqs.size == 1 &&
            reduced.constants.size == 1)
          Some(-reduced.arithConj.positiveEqs.head.constant)
        else
          None
      }
    }
  }

  /**
   * Evaluate the given formula in the current model.
   * This method can only be called after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>.
   */
  def eval(f : IFormula) : Boolean = evalPartial(f) getOrElse {
    // then we have to extend the model

    import TerForConvenience._

    f match {
      case IAtom(p, Seq())
        if (proofActorStatus == ProofActorStatus.AtPartialModel) => {
        // then we will just extend the partial model with a default value
        
        val a = Atom(p, List(), currentOrder)
        implicit val order = currentOrder
        currentModel = currentModel & a
        
        true
      }
      case f => {
        val p = new IExpression.Predicate("p", 0)
        implicit val extendedOrder = currentOrder extendPred p
        val extendedProver =
          currentProver.conclude(currentModel, extendedOrder)
                       .conclude(toInternal(IAtom(p, Seq()) </> f, extendedOrder)._1,
                                 extendedOrder)
    
        (extendedProver checkValidity true) match {
          case Left(m) if (!m.isFalse) => {
            val (reduced, _) = ReduceWithPredLits(m.predConj, Set(), extendedOrder)(p)
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, reduced.isTrue || reduced.isFalse)
            //-END-ASSERTION-///////////////////////////////////////////////////
            val result = reduced.isTrue
            val pf : Conjunction = p
        
            currentModel = ReduceWithConjunction(if (result) pf else !pf, extendedOrder)(m)
        
            result
          }
        }
      }
    }

  }

  /**
   * Evaluate the given formula in the current model, returning <code>None</code>
   * in case the model does not completely determine the value of the formula.
   * This method can only be called after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>.
   */
  def evalPartial(f : IFormula) : Option[Boolean] = {
    import TerForConvenience._
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, Set(ProverStatus.Sat,
                            ProverStatus.Invalid) contains getStatus(false))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    doDumpSMT {
      print("(get-value (")
      SMTLineariser(f)
      println("))")
    }
    
    f match {
      case IAtom(p, args) if (args forall (_.isInstanceOf[IIntLit])) => {
        if (!args.isEmpty)
          ensureFullModel
        
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
        ensureFullModel
        
        val reduced =
          ReduceWithConjunction(currentModel, functionalPreds, currentOrder)(
                                  toInternal(f, currentOrder)._1)
    
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
                       currentProver, currentOrder, existentialConstants,
                       functionEnc.clone,
                       arrayFuns, formulaeInProver,
                       currentPartitionNum,
                       constructProofs, mostGeneralConstraints,
                       validityMode, lastStatus,
                       currentModel, currentConstraint, currentCertificate)
    
    doDumpSMT {
      println("(push 1)")
    }
  }
  
  /**
   * Pop the top-most frame from the assertion stack.
   */
  def pop : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatus(false) != ProverStatus.Running)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (oldPreprocSettings, oldProver, oldOrder, oldExConstants,
         oldFunctionEnc, oldArrayFuns,
         oldFormulaeInProver, oldPartitionNum, oldConstructProofs,
         oldMGCs, oldValidityMode, oldStatus, oldModel, oldConstraint, oldCert) =
      storedStates.pop
    preprocSettings = oldPreprocSettings
    currentProver = oldProver
    currentOrder = oldOrder
    existentialConstants = oldExConstants
    functionEnc = oldFunctionEnc
    arrayFuns = oldArrayFuns
    formulaeInProver = oldFormulaeInProver
    currentPartitionNum = oldPartitionNum
    constructProofs = oldConstructProofs
    mostGeneralConstraints = oldMGCs
    formulaeTodo = false
    validityMode = oldValidityMode
    lastStatus = oldStatus
    currentModel = oldModel
    currentConstraint = oldConstraint
    currentCertificate = oldCert
    proofActorStatus = ProofActorStatus.Init
    
    doDumpSMT {
      println("(pop 1)")
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def flushTodo : Unit = formulaeTodo match {
    case IBoolLit(false) => // nothing
    case _ => {
      val (completeFor, axioms) = toInternal(formulaeTodo, currentOrder)
      formulaeTodo = false
      addToProver(completeFor, axioms)
    }
  }

  private def addToProver(completeFor : Conjunction,
                          axioms : Conjunction) : Unit = {
      formulaeInProver =
        (-1, axioms) :: (currentPartitionNum, completeFor) :: formulaeInProver

      proofActorStatus match {
        case ProofActorStatus.Init =>
          // nothing
        case ProofActorStatus.AtPartialModel | ProofActorStatus.AtFullModel =>
          if (completeFor.constants.isEmpty && axioms.isFalse) {
            // then we should be able to add this formula to the running prover
            proofActor ! AddFormulaCommand(completeFor)
          } else {
            proofActorStatus = ProofActorStatus.Init
          }
      }
      
      if (currentProver != null) {
        if ((IterativeClauseMatcher isMatchableRec completeFor) &&
            Seqs.disjoint(completeFor.constants, existentialConstants))
          currentProver =
            currentProver.conclude(List(completeFor, axioms), currentOrder)
        else
          currentProver = null
      }
  }
  
  private def resetModel = {
    currentModel = null
    currentConstraint = null
    currentCertificate = null
    lastStatus = ProverStatus.Unknown
  }
  
  private def addFormula(f : IFormula) : Unit = {
    resetModel
    doDumpSMT {
      print("(assert (not ")
      SMTLineariser(f)
      println("))")
    }
    formulaeTodo = formulaeTodo | f
  }

  private def addFormula(f : Formula) : Unit = {
    resetModel
    doDumpSMT {
      print("; adding internal formula: " + f)
    }
    addToProver(Conjunction.conj(f, currentOrder), Conjunction.FALSE)
  }

  private def toInternal(f : IFormula,
                         order : TermOrder) : (Conjunction, Conjunction) = {
    val sig = new Signature(Set(),
                            existentialConstants,
                            order.orderedConstants -- existentialConstants,
                            order)
    val (fors, _, newSig) =
      Preprocessing(INamedPart(FormulaPart, f), List(), sig, preprocSettings, functionEnc)
    functionEnc.clearAxioms
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, order == newSig.order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = 
      ReduceWithConjunction(Conjunction.TRUE, functionalPreds, order)(
        Conjunction.conj(InputAbsy2Internal(
          IExpression.connect(for (INamedPart(FormulaPart, f) <- fors.iterator)
                                yield f,
                              IBinJunctor.Or), order), order))
    val axioms = 
      ReduceWithConjunction(Conjunction.TRUE, functionalPreds, order)(
        Conjunction.conj(InputAbsy2Internal(
          IExpression.connect(for (INamedPart(PartName.NO_NAME, f) <- fors.iterator)
                                yield f,
                              IBinJunctor.Or), order), order))
    (formula, axioms)
  }
  
  private def goalSettings = {
    var gs = GoalSettings.DEFAULT
//    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
//    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs,
        (for ((p, f) <- functionEnc.predTranslation.iterator; if (!f.partial))
         yield p).toSet)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs
  }

  private var preprocSettings : PreprocessingSettings = _
  private var currentOrder : TermOrder = _
  private var existentialConstants : Set[IExpression.ConstantTerm] = _
  private var functionEnc : FunctionEncoder = _
  private var currentProver : ModelSearchProver.IncProver = _
  private var currentModel : Conjunction = _
  private var currentConstraint : Conjunction = _
  private var currentCertificate : Certificate = _
  private var formulaeInProver : List[(Int, Conjunction)] = List()
  private var currentPartitionNum : Int = -1
  private var constructProofs : Boolean = false
  private var mostGeneralConstraints : Boolean = false
  private var formulaeTodo : IFormula = false
  
  private val storedStates = new ArrayStack[(PreprocessingSettings,
                                             ModelSearchProver.IncProver,
                                             TermOrder,
                                             Set[IExpression.ConstantTerm],
                                             FunctionEncoder,
                                             Map[Int, (IFunction, IFunction)],
                                             List[(Int, Conjunction)],
                                             Int,
                                             Boolean,
                                             Boolean,
                                             Boolean,
                                             ProverStatus.Value,
                                             Conjunction,
                                             Conjunction,
                                             Certificate)]
  
  private def recreateProver = {
    preprocSettings =
      Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
             preprocSettings, functionEnc.predTranslation.values.toSet)
    if (currentProver != null)
      currentProver = (ModelSearchProver emptyIncProver goalSettings)
                          .conclude(formulaeInProver.unzip._2, currentOrder)
  }
  
  private def functionalPreds = functionEnc.predTranslation.keySet.toSet
  
  //////////////////////////////////////////////////////////////////////////////
  //
  // Prover actor, for the hard work
  
  private val proverRes = new SyncVar[ProverResult]
  private var lastStatus : ProverStatus.Value = _
  private var validityMode : Boolean = _
  
  private var proofActorStatus : ProofActorStatus.Value = _
  
  private val proofActor = actor {
    Debug enableAllAssertions enableAssert
    
    var cont = true
    var nextCommand : ProverCommand = null
    
    def directorWaitForNextCmd(model : Conjunction) = {
      var res : ModelSearchProver.SearchDirection = null
      var forsToAdd = List[Conjunction]()
              
      while (res == null) receive {
        case DeriveFullModelCommand =>
          res = ModelSearchProver.DeriveFullModelDir
        case NextModelCommand =>
          res = ModelSearchProver.NextModelDir
        case RecheckCommand =>
          res = ModelSearchProver.AddFormulaDir(
                 Conjunction.conj(forsToAdd, model.order))
        case AddFormulaCommand(formula) =>
          forsToAdd = formula :: forsToAdd
        case c : ProverCommand => {
          // get out of here
          nextCommand = c
          res = ModelSearchProver.ReturnSatDir
        }
      }
              
      res
    }
    
    val commandParser : PartialFunction[Any, Unit] = {
      case CheckSatCommand(p) =>
          
        Timeout.catchTimeout {
          p.checkValidityDir {
            case (model, false) => {
              proverRes set SatPartialResult(model)
              directorWaitForNextCmd(model)
            }
            
            case (model, true) => {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertPre(AC, !model.isFalse)
              //-END-ASSERTION-/////////////////////////////////////////////////
              
              proverRes set SatResult(model)
              directorWaitForNextCmd(model)
            }
          }
        } { case _ => null } match {

          case null =>
            proverRes set StoppedResult
          case Left(m) if (nextCommand == null) =>
            proverRes set UnsatResult
          case Left(_) =>
            // nothing
          case Right(cert) =>
            proverRes set UnsatCertResult(cert)
              
        }

      case CheckValidityCommand(formula, goalSettings, mgc) =>
        
        Timeout.catchTimeout {
          
          (new ExhaustiveProver (!mgc, goalSettings))(formula, formula.order)
          
        } { case _ => null } match {
          
          case null =>
            proverRes set StoppedResult
          case tree => {
            val constraint = tree.closingConstraint
            if (constraint.isFalse) {
              proverRes set InvalidResult
            } else {
              val solution = ModelSearchProver(constraint.negate, constraint.order)
              proverRes set FoundConstraintResult(constraint, solution)
            }
          }
            
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
      
      val oldPartitionNum = currentPartitionNum
      setPartitionNumber(-1)
      addFormula(!Parser2InputAbsy.arrayAxioms(arity, select, store))
      setPartitionNumber(oldPartitionNum)
      
      (select, store)
    })
  
  //////////////////////////////////////////////////////////////////////////////

  reset

}