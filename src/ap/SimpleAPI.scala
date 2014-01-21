/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2014 Philipp Ruemmer <ph_r@gmx.net>
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
                               IterativeClauseMatcher, Quantifier,
                               LazyConjunction}
import ap.theories.{Theory, TheoryCollector}
import ap.proof.theoryPlugins.Plugin
import ap.util.{Debug, Timeout, Seqs}

import scala.collection.mutable.{HashMap => MHashMap, ArrayStack,
                                 LinkedHashMap}
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.concurrent.SyncVar

object SimpleAPI {
  
  private val AC = Debug.AC_SIMPLE_API

  private val SMTDumpBasename = "smt-queries-"
  private val ScalaDumpBasename = "princess-queries-"
  
  /**
   * Create a new prover. Note that the prover has to be shut down explicitly
   * by calling the method <code>SimpleAPI.shutDown</code> after use.
   */
  def apply(enableAssert : Boolean = false,
            dumpSMT : Boolean = false,
            smtDumpBasename : String = SMTDumpBasename,
            dumpScala : Boolean = false,
            scalaDumpBasename : String = ScalaDumpBasename,
            tightFunctionScopes : Boolean = true) : SimpleAPI =
    new SimpleAPI (enableAssert,
                   if (dumpSMT) Some(smtDumpBasename) else None,
                   if (dumpScala) Some(scalaDumpBasename) else None,
                   tightFunctionScopes)

  def spawn : SimpleAPI = apply()

  def spawnWithAssertions : SimpleAPI = apply(enableAssert = true)

  def spawnWithLog : SimpleAPI = apply(dumpSMT = true)

  def spawnWithLog(basename : String) : SimpleAPI =
    apply(dumpSMT = true, smtDumpBasename = basename)

  def spawnWithScalaLog : SimpleAPI = apply(dumpScala = true)

  def spawnWithScalaLog(basename : String) : SimpleAPI =
    apply(dumpScala = true, scalaDumpBasename = basename)
  
  /**
   * Run the given function with a fresh prover, and shut down the prover
   * afterwards.
   */
  def withProver[A](f : SimpleAPI => A) : A = {
    val p = apply()
    try {
      f(p)
    } finally {
      p.shutDown
    }
  }
  
  /**
   * Run the given function with a fresh prover, and shut down the prover
   * afterwards.
   */
  def withProver[A](enableAssert : Boolean = false,
                    dumpSMT : Boolean = false,
                    smtDumpBasename : String = SMTDumpBasename,
                    dumpScala : Boolean = false,
                    scalaDumpBasename : String = ScalaDumpBasename,
                    tightFunctionScopes : Boolean = true)
                   (f : SimpleAPI => A) : A = {
    val p = apply(enableAssert,
                  dumpSMT, smtDumpBasename,
                  dumpScala, scalaDumpBasename,
                  tightFunctionScopes)
    try {
      f(p)
    } finally {
      p.shutDown
    }
  }
  
  /**
   * Pretty-print a formula or term.
   */
  def pp(f : IExpression) : String =
    DialogUtil asString { PrincessLineariser printExpression f }
  
  //////////////////////////////////////////////////////////////////////////////
  
  object ProverStatus extends Enumeration {
    val Sat, Unsat, Invalid, Valid, Unknown, Running, Error = Value
  }

  object TimeoutException extends Exception("Timeout during ap.SimpleAPI call")

  //////////////////////////////////////////////////////////////////////////////

  class PartialModel(
         val interpretation : scala.collection.Map[ModelLocation, ModelValue]) {

    import IExpression._

    def definedLocations = interpretation.keySet

    def evalExpression(e : IExpression) : Option[ModelValue] =
      Evaluator.visit(e, ())
    def eval(t : ITerm) : Option[IdealInt] =
      for (IntValue(v) <- evalExpression(t)) yield v
    def eval(f : IFormula) : Option[Boolean] =
      for (BoolValue(b) <- evalExpression(f)) yield b

    override def toString =
      "{" +
      (for ((l, v) <- interpretation.iterator)
       yield ("" + l + " -> " + v)).mkString(", ") +
      "}"

    private object Evaluator
            extends CollectingVisitor[Unit, Option[ModelValue]] {
      def postVisit(t : IExpression, arg : Unit,
                    subres : Seq[Option[ModelValue]]) = t match {
        ////////////////////////////////////////////////////////////////////////
        // Terms
        case IIntLit(v) =>
          Some(IntValue(v))
        case IConstant(c) =>
          interpretation get ConstantLoc(c)
        case ITimes(coeff, _) =>
          for (IntValue(v) <- subres(0)) yield IntValue(v * coeff)
        case _ : IPlus =>
          for (IntValue(v1) <- subres(0); IntValue(v2) <- subres(1))
          yield IntValue(v1 + v2)
        case IFunApp(f, _) => {
          val actualArgs = for (Some(IntValue(v)) <- subres) yield v
          if (actualArgs.size == f.arity)
            interpretation get IntFunctionLoc(f, actualArgs)
          else
            None
        }
        case _ : ITermITE =>
          for (BoolValue(b) <- subres(0);
               r <- subres(if (b) 1 else 2)) yield r
        ////////////////////////////////////////////////////////////////////////
        // Formulas
        case IBoolLit(b) =>
          Some(BoolValue(b))
        case _ : INot =>
          for (BoolValue(b) <- subres(0)) yield BoolValue(!b)
        case IBinFormula(IBinJunctor.And, _, _) => subres match {
          case Seq(v@Some(BoolValue(false)), _) => v
          case Seq(_, v@Some(BoolValue(false))) => v
          case Seq(Some(BoolValue(true)), v)    => v
          case Seq(v, Some(BoolValue(true)))    => v
          case _                                => None
        }
        case IBinFormula(IBinJunctor.Or, _, _) => subres match {
          case Seq(v@Some(BoolValue(true)), _)  => v
          case Seq(_, v@Some(BoolValue(true)))  => v
          case Seq(Some(BoolValue(false)), v)   => v
          case Seq(v, Some(BoolValue(false)))   => v
          case _                                => None
        }
        case IBinFormula(IBinJunctor.Eqv, _, _) =>
          for (BoolValue(v1) <- subres(0); BoolValue(v2) <- subres(1))
          yield BoolValue(v1 == v2)
        case IAtom(p, _) => {
          val actualArgs = for (Some(IntValue(v)) <- subres) yield v
          if (actualArgs.size == p.arity)
            interpretation get PredicateLoc(p, actualArgs)
          else
            None
        }
        case IIntFormula(IIntRelation.EqZero, _) =>
          for (IntValue(v) <- subres(0)) yield BoolValue(v.isZero)
        case IIntFormula(IIntRelation.GeqZero, _) =>
          for (IntValue(v) <- subres(0)) yield BoolValue(v.signum >= 0)
        case _ : IFormulaITE =>
          for (BoolValue(b) <- subres(0);
               r <- subres(if (b) 1 else 2)) yield r
        case _ : INamedPart =>
          subres(0)
      }
    }
  }

  abstract sealed class ModelLocation
  case class ConstantLoc(c : IExpression.ConstantTerm)
                                     extends ModelLocation {
    override def toString = c.toString
  }
  case class IntFunctionLoc(f : IFunction, args : Seq[IdealInt])
                                     extends ModelLocation {
    override def toString =
      f.name + (if (args.isEmpty) "" else "(" + (args mkString ", ") + ")")
  }
  case class PredicateLoc(p : IExpression.Predicate, args : Seq[IdealInt])
                                     extends ModelLocation {
    override def toString =
      p.name + (if (args.isEmpty) "" else "(" + (args mkString ", ") + ")")
  }
  
  abstract sealed class ModelValue
  case class IntValue(v : IdealInt)  extends ModelValue {
    override def toString = v.toString
  }
  case class BoolValue(v : Boolean)  extends ModelValue {
    override def toString = v.toString
  }

  //////////////////////////////////////////////////////////////////////////////

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
class SimpleAPI private (enableAssert : Boolean,
                         dumpSMT : Option[String],
                         dumpScala : Option[String],
                         tightFunctionScopes : Boolean) {

  import SimpleAPI._

  Debug enableAllAssertions enableAssert

  private val dumpSMTStream = dumpSMT match {
    case Some(basename) => {
      val dumpSMTFile = java.io.File.createTempFile(basename, ".smt2")
      new java.io.FileOutputStream(dumpSMTFile)
    }
    case None => null
  }
  
  private def doDumpSMT(comp : => Unit) =
    if (dumpSMT != None) Console.withOut(dumpSMTStream) {
      comp
    }
  
  private val dumpScalaStream = dumpScala match {
    case Some(basename) => {
      val dumpScalaFile = java.io.File.createTempFile(basename, ".scala")
      new java.io.FileOutputStream(dumpScalaFile)
    }
    case None => null
  }
  
  private def doDumpScala(comp : => Unit) =
    if (dumpScala != None) Console.withOut(dumpScalaStream) {
      comp
    }
  
  private var dumpScalaNum = 0

  private def getScalaNum = {
    val res = dumpScalaNum
    dumpScalaNum = dumpScalaNum + 1
    res
  }

  def shutDown : Unit = {
    proofActor ! ShutdownCommand
    doDumpSMT {
      println("(exit)")
    }
    doDumpScala {
      closeAllScopes
      println("}} // withProver")
    }
  }

  doDumpScala {
    println("import ap._")
    println("import ap.parser._")
    println
    println("SimpleAPI.withProver { p =>")
    println("import p._")
    println("import IExpression._")
    println("{")
    println
  }
  
  private val basicPreprocSettings =
    Param.TIGHT_FUNCTION_SCOPES.set(PreprocessingSettings.DEFAULT,
                                    tightFunctionScopes)

  private def closeAllScopes = {
    for (_ <- 0 until storedStates.size)
      println("} // pop scope")
    println
  }

  def reset = {
    doDumpSMT {
      println("(reset)")
      println("(set-logic AUFLIA)")
    }
    doDumpScala {
      closeAllScopes
      println("reset")
      println("}")
      println("{")
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatusHelp(false) != ProverStatus.Running)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    storedStates.clear
    
    preprocSettings = basicPreprocSettings
    currentOrder = TermOrder.EMPTY
    existentialConstants = Set()
    functionalPreds = Set()
    functionEnc =
      new FunctionEncoder(Param.TIGHT_FUNCTION_SCOPES(preprocSettings), false)
    currentProver = ModelSearchProver emptyIncProver goalSettings
    formulaeInProver = List()
    formulaeTodo = false
    currentModel = Conjunction.TRUE
    decoderDataCache.clear
    lastPartialModel = null
    currentConstraint = null
    currentCertificate = null
    lastStatus = ProverStatus.Sat
    validityMode = false
    proofActorStatus = ProofActorStatus.Init
    currentPartitionNum = -1
    constructProofs = false
    mostGeneralConstraints = false
    theoryPlugin = None
    theoryCollector = new TheoryCollector
  }

  private var currentDeadline : Option[Long] = None

  /**
   * Run a block of commands for at most <code>millis</code> milli-seconds.
   * After this, calls to <code>???</code>, <code>checkSat(true)</code>,
   * <code>nextModel(true)</code>, <code>getStatus(true)</code> will throw a
   * <code>TimeoutException</code>.
   */
  def withTimeout[A](millis : Long)(comp : => A) = {
    val oldDeadline = currentDeadline
    currentDeadline = Some(System.currentTimeMillis + millis)
    try {
      comp
    } finally {
      currentDeadline = oldDeadline
    }
  }

  private def checkTimeout = currentDeadline match {
    case Some(deadline) =>
      if (System.currentTimeMillis > deadline)
        throw TimeoutException
    case None =>
      // nothing
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
  def createConstantRaw(rawName : String) : IExpression.ConstantTerm =
    createConstantRaw(rawName, "createConstant")

  private def createConstantRaw(rawName : String,
                                scalaCmd : String) : IExpression.ConstantTerm = {
    flushTodo

    import IExpression._
    
    val name = sanitise(rawName)
    val c = new ConstantTerm(name)
    currentOrder = currentOrder extend c
    restartProofActor
    doDumpSMT {
      println("(declare-fun " + name + " () Int)")
    }
    doDumpScala {
      println("val " + name + " = " + scalaCmd + "(\"" + rawName + "\")")
    }
    c
  }

  /**
   * Create a sequence of new symbolic constants, without directly turning them into an
   * <code>ITerm</code>. This method is
   * only useful when working with formulae in the internal prover format.
   */
  def createConstantsRaw(prefix : String, nums : Range)
                        : IndexedSeq[IExpression.ConstantTerm] =
    createConstantsRaw(prefix, nums, "createConstant")

  def createConstantsRaw(prefix : String, nums : Range, scalaCmd : String)
                        : IndexedSeq[IExpression.ConstantTerm] = {
    flushTodo

    import IExpression._
    val cs = (for (i <- nums)
              yield {
                doDumpSMT {
                  println("(declare-fun " + (prefix + i) + " () Int)")
                }
                doDumpScala {
                  println("val " + prefix + i +
                          " = " + scalaCmd + "(\"" + prefix + i + "\")")
                }
                new ConstantTerm (prefix + i)
              }).toIndexedSeq
    currentOrder = currentOrder extend cs
    restartProofActor
    cs
  }

  /**
   * Create a new symbolic constant that is implicitly existentially quantified.
   */
  def createExistentialConstant(rawName : String) : ITerm = {
    import IExpression._
    val c = createConstantRaw(rawName, "createExistentialConstant")
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
    val cs = createConstantsRaw("X", start until (start + num),
                                "createExistentialConstant")
    existentialConstants = existentialConstants ++ cs
    for (c <- cs) yield IConstant(c)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an externally defined constant to the environment of this prover.
   */
  def addConstant(c : IExpression.ConstantTerm) : Unit = {
    flushTodo

    currentOrder = currentOrder extend c
    restartProofActor
    doDumpSMT {
      println("(declare-fun " + c.name + " () Int)")
    }
    doDumpScala {
      println("val " + c.name + " = " + "createConstant(\"" + c.name + "\") " +
              "// addConstant(" + c.name + ")")
    }
  }

  /**
   * Add a sequence of externally defined constant to the environment of
   * this prover.
   */
  def addConstants(cs : Iterable[IExpression.ConstantTerm]) : Unit = {
    flushTodo

    currentOrder = currentOrder extend cs.toSeq
    restartProofActor
    doDumpSMT {
      for (c <- cs)
        println("(declare-fun " + c.name + " () Int)")
    }
    doDumpScala {
      for (c <- cs)
        println("val " + c.name + " = " + "createConstant(\"" + c.name + "\") " +
                "// addConstant(" + c.name + ")")
    }
  }

  /**
   * Create a new Boolean variable (nullary predicate).
   */
  def createBooleanVariable(rawName : String) : IFormula = {
    flushTodo

    import IExpression._
    
    val name = sanitise(rawName)
    val p = new Predicate(name, 0)
    currentOrder = currentOrder extendPred p
    restartProofActor
    doDumpSMT {
      println("(declare-fun " + name + " () Bool)")
    }
    doDumpScala {
      println("val " + name + " = " +
              "createBooleanVariable(\"" + rawName + "\")")
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
    flushTodo

    import IExpression._
    val startInd = currentOrder.orderedPredicates.size
    val ps = (for (i <- 0 until num)
              yield {
                doDumpSMT {
                  println("(declare-fun " + ("p" + (startInd + i)) + " () Bool)")
                }
                doDumpScala {
                  println("val " + ("p" + (startInd + i)) +
                          " = " + "createBooleanVariable(\"" +
                          ("p" + (startInd + i)) + "\")")
                }
                new Predicate ("p" + (startInd + i), 0)
              }).toIndexedSeq
    currentOrder = currentOrder extendPred ps
    restartProofActor
    for (p <- ps) yield p()
  }

  /**
   * Create a new uninterpreted function with fixed arity.
   */
  def createFunction(rawName : String, arity : Int) : IFunction = {
    doDumpScala {
      println("val " + sanitise(rawName) + " = " +
              "createFunction(\"" + rawName + "\", " + arity + ")")
    }
    createFunctionHelp(rawName, arity)
  }

  private def createFunctionHelp(rawName : String, arity : Int) : IFunction = {
    flushTodo

    val name = sanitise(rawName)
    val f = new IFunction(name, arity, true, false)
    // make sure that the function encoder knows about the function
    val (_, newOrder) =
      functionEnc.apply(IFunApp(f, List.fill(arity)(0)) === 0, currentOrder)
    functionalPreds = functionalPreds ++ functionEnc.predTranslation.keysIterator
    doDumpSMT {
      println("(declare-fun " + name + " (" +
          (for (_ <- 0 until arity) yield "Int").mkString(" ") + ") Int)")
    }
    currentOrder = newOrder
    recreateProver
    f
  }

  /**
   * Create a new uninterpreted Boolean-valued function with fixed arity.
   * Booleans values are encoded into integers,
   * mapping <code>true</code> to <code>0</code> and <code>false</code>
   * to <code>1</code>.<br>
   * In contrast to predicates (generated using <code>createRelation</code>),
   * Boolean functions can be used within triggers.
   */
  def createBooleanFunction(rawName : String,
                            arity : Int) : IExpression.BooleanFunApplier =
    new IExpression.BooleanFunApplier({
      doDumpScala {
        println("// createBooleanFunction" +
                "(\"" + rawName + "\", " + arity + ")")
      }
      createFunction(rawName, arity)
    })
  
  /**
   * Create a new uninterpreted predicate with fixed arity.<br>
   * Predicates are more low-level than Boolean functions, and
   * cannot be used within triggers.
   */
  def createRelation(rawName : String, arity : Int) = {
    flushTodo

    import IExpression._
    
    val name = sanitise(rawName)
    val r = new Predicate(name, arity)
    currentOrder = currentOrder extendPred r
    restartProofActor
    doDumpSMT {
      println("(declare-fun " + name + " (" +
          (for (_ <- 0 until arity) yield "Int").mkString(" ") + ") Bool)")
    }
    doDumpScala {
      println("val " + name + " = " +
              "createRelation(\"" + rawName + "\", " + arity + ")")
    }
    r
  }
  
  /**
   * Export the current <code>TermOrder</code> of the prover. This method is
   * only useful when working with formulae in the internal prover format.
   */
  def order = {
    // flush, to make sure that all theories required by earlier formulas
    // are loaded
    flushTodo
    currentOrder
  }
  
  /**
   * The theories currectly loaded in this prover.
   */
  def theories : Seq[Theory] = {
    flushTodo
    theoryCollector.theories
  }

  /**
   * Convert a formula in input syntax to the internal prover format.
   */
  def asConjunction(f : IFormula) : Conjunction = {
    flushTodo
    ReduceWithConjunction(Conjunction.TRUE, functionalPreds, currentOrder)(
      toInternalNoAxioms(f, currentOrder))
  }
  
  /**
   * Pretty-print a formula or term.
   */
  def pp(f : IExpression) : String = SimpleAPI.pp(f)
  
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
  def addAssertion(assertion : IFormula) : Unit = {
    doDumpScala {
      print("!! (")
      PrettyScalaLineariser(getFunctionNames)(assertion)
      println(")")
    }
    addFormula(!assertion)
  }
  
  /**
   * Add an assertion to the prover: assume that the given formula is true
   */
  def addAssertion(assertion : Formula) : Unit = {
    doDumpScala {
      println("// addAssertion(" + assertion + ")")
    }
    addFormula(!LazyConjunction(assertion)(currentOrder))
  }
    
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
    doDumpScala {
      print("?? (")
      PrettyScalaLineariser(getFunctionNames)(conc)
      println(")")
    }
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
    doDumpScala {
      println("// addConclusion(" + conc + ")")
    }
    addFormula(LazyConjunction(conc)(currentOrder))
  }
  
  /**
   * Determine the status of the formulae asserted up to this point. This
   * call is blocking, but will not run the prover repeatedly if nothing
   * has changed since the last check.
   */
  def ??? = {
    doDumpSMT {
      println("(check-sat)")
    }
    doDumpScala {
      println("println(\"" + getScalaNum + ": \" + ???)")
    }
    checkTimeout
    getStatusHelp(true) match {
      case ProverStatus.Unknown => checkSatHelp(true)
      case res => res
    }
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
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + checkSat(true))")
      if (!block)
        print(" // checkSat(" + block + ")")
      println
    }

    if (block)
      checkTimeout

    checkSatHelp(block)
  }
  
  private def checkSatHelp(block : Boolean) : ProverStatus.Value =
    getStatusHelp(false) match {
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
            restartProofActor
            proofActor ! RecheckCommand
          }
        }
    
        getStatusWithDeadline(block)    
      }
      
      case ProverStatus.Running => {
        assert(false)
        ProverStatus.Error
      }
        
      case s => s
    }

  /**
   * After a <code>Sat</code> result, continue searching for the next model.
   * In most ways, this method behaves exactly like <code>checkSat</code>.
   */
  def nextModel(block : Boolean) : ProverStatus.Value = {
    doDumpSMT {
      println("; (next-model)")
    }
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + nextModel(true))")
      if (!block)
        print(" // nextModel(" + block + ")")
      println
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatusHelp(false) == ProverStatus.Sat)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (block)
      checkTimeout

    lastStatus = ProverStatus.Running
    proverRes.unset
    
    proofActor ! NextModelCommand
    getStatusWithDeadline(block)
  }

  private def getStatusWithDeadline(block : Boolean) : ProverStatus.Value =
    currentDeadline match {
      case Some(deadline) if (block) =>
        getStatusHelp(deadline - System.currentTimeMillis) match {
          case ProverStatus.Running => {
            stop
            throw TimeoutException
          }
          case s => s
        }
      case _ =>
        getStatusHelp(block)
    }

  /**
   * Query result of the last <code>checkSat</code> or <code>nextModel</code>
   * call. Will block until a result is available if <code>block</code>
   * argument is true, otherwise return immediately.
   */
  def getStatus(block : Boolean) : ProverStatus.Value = {
    doDumpScala {
      println("// getStatus(" + block + ")")
    }
    if (block)
      checkTimeout
    getStatusWithDeadline(block)
  }

  private def getStatusHelp(block : Boolean) : ProverStatus.Value = {
    if (lastStatus == ProverStatus.Running && (block || proverRes.isSet))
      evalProverResult(proverRes.get)
    lastStatus
  }
  
  /**
   * Query result of the last <code>checkSat</code> or <code>nextModel</code>
   * call. Will block until a result is available, or until <code>timeout</code>
   * milli-seconds elapse.
   */
  def getStatus(timeout : Long) : ProverStatus.Value = {
    doDumpScala {
      println("// getStatus(" + timeout + ")")
    }
    getStatusHelp(timeout)
  }
  
  private def getStatusHelp(timeout : Long) : ProverStatus.Value = {
    if (lastStatus == ProverStatus.Running)
      for (r <- proverRes.get(timeout))
        evalProverResult(r)
    lastStatus
  }

  private def evalProverResult(pr : ProverResult) : Unit = pr match {
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
  
  /**
   * Stop a running prover. If the prover had already terminated, give same
   * result as <code>getResult</code>, otherwise <code>Unknown</code>.
   */
  def stop : ProverStatus.Value = {
    doDumpScala {
      println("// stop")
    }
    getStatusHelp(false) match {
      case ProverStatus.Running => {
        proofActor ! StopCommand
        getStatusHelp(true)
      }
      case res =>
        res
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add subsequent formulae to partition <code>num</code>.
   *  Index <code>-1</code> represents
   * formulae belonging to all partitions (e.g., theory axioms).
   */
  def setPartitionNumber(num : Int) : Unit = {
    doDumpScala {
      println("setPartitionNumber(" + num + ")")
    }
    setPartitionNumberHelp(num)
  }

  private def setPartitionNumberHelp(num : Int) : Unit =
    if (currentPartitionNum != num) {
      flushTodo
      currentPartitionNum = num
    }
  
  /**
   * Construct proofs in subsequent <code>checkSat</code> calls. Proofs are
   * needed for extract interpolants.
   */
  def setConstructProofs(b : Boolean) : Unit = if (constructProofs != b) {
    doDumpScala {
      println("setConstructProofs(" + b + ")")
    }
    constructProofs = b
    recreateProver
  }

  /**
   * Compute an inductive sequence of interpolants, for the given
   * partitioning of the input problem.
   */
  def getInterpolants(partitions : Seq[Set[Int]]) : Seq[IFormula] = {
    doDumpSMT {
      println("; (get-interpolants)")
    }
    doDumpScala {
      println("println(\"" + getScalaNum + ": \" + getInterpolants(List(" + (
        for (s <- partitions.iterator)
        yield ("Set(" + s.mkString(", ") + ")")).mkString(", ") + ")))")
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (Set(ProverStatus.Unsat,
                             ProverStatus.Valid) contains getStatusHelp(false)) &&
                        currentCertificate != null)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  
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
   * Install a theory plugin in the prover.
   * This is highly experimental functionality.
   *
   * (In particular, <code>eval</code> and <code>evalPartial</code> might
   * sometimes produce strange results in combination with plugins)
   */
  def setupTheoryPlugin(plugin : Plugin) : Unit = {
    doDumpSMT {
      println("; (setup-theory-plugin)")
    }
    doDumpScala {
      println("// setupTheoryPlugin")
    }
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // Multiple theory plugins are currently unsupported
    Debug.assertPre(AC, theoryPlugin == None)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    theoryPlugin = Some(plugin)
    recreateProver
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add a new theory to the prover. Normally, calling this function is not
   * necessary, since theories in asserted formulae will be detected
   * automatically.
   */
  def addTheory(newTheory : Theory) : Unit =
    addTheories(List(newTheory))

  /**
   * Add new theories to the prover. Normally, calling this function is not
   * necessary, since theories in asserted formulae will be detected
   * automatically.
   */
  def addTheories(newTheories : Seq[Theory]) : Unit = {
    doDumpSMT {
      println("; (add-theories " + (newTheories mkString " ") + ")")
    }
    doDumpScala {
      println("// addTheories(List(" + (newTheories mkString ", ") + "))")
    }
    for (t <- newTheories)
      theoryCollector addTheory t
    addTheoryAxioms
  }
  
  private def addTheoryAxioms = {
    val theoryAxioms = checkNewTheories
    if (!theoryAxioms.isEmpty) {
      val oldPartitionNum = currentPartitionNum
      setPartitionNumberHelp(-1)
      for (f <- theoryAxioms)
        addFormula(LazyConjunction(f)(currentOrder))
      setPartitionNumberHelp(oldPartitionNum)
    }
  }

  /**
   * Add all theories to the prover that occur in the given order.
   */
  def addTheoriesFor(order : TermOrder) : Unit = {
    theoryCollector(order)
    addTheoryAxioms
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * In subsequent <code>checkSat</code> calls for problems with existential
   * constants, infer the most general constraint on existential constants
   * satisfying the problem. NB: If this option is used wrongly, it might
   * lead to non-termination of the prover.
   */
  def setMostGeneralConstraints(b : Boolean) : Unit = {
    doDumpSMT {
      println("; (set-most-general-constraints " + b + ")")
    }
    doDumpScala {
      println("setMostGeneralConstraints(" + b + ")")
    }
    mostGeneralConstraints = b
  }
  
  /**
   * After receiving the result
   * <code>ProverStatus.Unsat</code> or <code>ProverStates.Valid</code>
   * for a problem that contains existential constants, return a (satisfiable)
   * constraint over the existential constants that describes satisfying
   * assignments of the existential constants.
   */
  def getConstraint : IFormula = {
    doDumpSMT {
      println("; (get-constraint)")
    }
    doDumpScala {
      println("println(\"" + getScalaNum + ": \" + getConstraint)")
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, Set(ProverStatus.Unsat,
                            ProverStatus.Valid) contains getStatusHelp(false))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    (new Simplifier)(Internal2InputAbsy(currentConstraint, Map()))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def ensureFullModel =
    while (proofActorStatus != ProofActorStatus.AtFullModel)
      if (proofActorStatus == ProofActorStatus.AtPartialModel) {
        // let's get a complete model
        lastStatus = ProverStatus.Running
        proverRes.unset
        proofActor ! DeriveFullModelCommand
        getStatusHelp(true)
      } else {
        // then we have to completely re-run the prover
        lastStatus = ProverStatus.Unknown
        checkSatHelp(true)
      }

  /**
   * Produce a partial model, i.e., a (usually) partial interpretation
   * of constants, functions, and predicates. This method can be
   * called in two situations:
   * <ul>
   *    <li> after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>, or</li>
   * <li> after receiving
   * the result
   * <code>ProverStatus.Unsat</code> or <code>ProverStates.Valid</code>
   * for a problem that contains existential constants. In this case the
   * model only assigns existential constants.
   * </li>
   * </ul>
   */
  def partialModel : PartialModel = {
    doDumpSMT {
      println("; (partial-model)")
    }
    doDumpScala {
      println("partialModel")
    }

    if (lastPartialModel != null) {
      lastPartialModel
    } else {
      import IExpression._
  
      setupTermEval
  
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(SimpleAPI.AC,
                      currentModel.arithConj.negativeEqs.isTrue &&
                      currentModel.arithConj.inEqs.isTrue &&
                      currentModel.negatedConjs.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
  
      val interpretation = new LinkedHashMap[ModelLocation, ModelValue]
  
      for (l <- currentModel.arithConj.positiveEqs) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(SimpleAPI.AC,
                        l.constants.size == 1 && l.variables.isEmpty &&
                        l.leadingCoeff.isOne)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        interpretation.put(ConstantLoc(l.leadingTerm.asInstanceOf[ConstantTerm]),
                           IntValue(-l.constant))
      }
  
      for (a <- currentModel.predConj.positiveLits) {
        val argValues =
          (for (l <- a.iterator) yield {
             //-BEGIN-ASSERTION-////////////////////////////////////////////////
             Debug.assertInt(SimpleAPI.AC,
                             l.constants.isEmpty && l.variables.isEmpty)
             //-END-ASSERTION-//////////////////////////////////////////////////
             l.constant
           }).toIndexedSeq
        (functionEnc.predTranslation get a.pred) match {
          case Some(f) =>
            interpretation.put(IntFunctionLoc(f, argValues.init),
                               IntValue(argValues.last))
          case None =>
            interpretation.put(PredicateLoc(a.pred, argValues),
                               BoolValue(true))
        }
      }
  
      for (a <- currentModel.predConj.negativeLits)
        if (!(functionEnc.predTranslation contains a.pred)) {
          val argValues =
            (for (l <- a.iterator) yield {
               //-BEGIN-ASSERTION-//////////////////////////////////////////////
               Debug.assertInt(SimpleAPI.AC,
                               l.constants.isEmpty && l.variables.isEmpty)
               //-END-ASSERTION-////////////////////////////////////////////////
               l.constant
             }).toIndexedSeq
          interpretation.put(PredicateLoc(a.pred, argValues),
                             BoolValue(false))
        }
  
      lastPartialModel = new PartialModel (interpretation)
      lastPartialModel
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Decoding data needed (and implicitly read) by theories.
   */
  val decoderContext = new Theory.DecoderContext {
    def getDataFor(t : Theory) : Theory.TheoryDecoderData =
      decoderDataCache.getOrElseUpdate(t, {
        setupTermEval
        (t generateDecoderData currentModel).get
      })
  }

  private val decoderDataCache = new MHashMap[Theory, Theory.TheoryDecoderData]

  //////////////////////////////////////////////////////////////////////////////

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
  def eval(t : ITerm) : IdealInt = {
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + eval(")
      PrettyScalaLineariser(getFunctionNames)(t)
      println("))")
    }

    t match {
      case IConstant(c) => evalHelp(c)
      
      case t if (currentOrder.orderedPredicates forall (_.arity == 0)) => {
        // we first try to reduce the expression, and then assume that all
        // unassigned constants have the value 0
        
        val (reduced, c, extendedOrder) = reduceTerm(t)
            
        val unassignedConsts = reduced.constants - c
        val finalReduced =
          if (unassignedConsts.isEmpty) {
            reduced
          } else {
            import TerForConvenience._
            implicit val o = extendedOrder
            // TODO: we need to do the same for Boolean variables?
            ReduceWithConjunction(unassignedConsts.toSeq === 0, extendedOrder)(
                                  reduced)
          }
        
        //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        finalReduced.isLiteral &&
                        finalReduced.arithConj.positiveEqs.size == 1 &&
                        finalReduced.constants.size == 1)
        //-END-ASSERTION-/////////////////////////////////////////////////////////
        
        -finalReduced.arithConj.positiveEqs.head.constant
      }
      
      case t => evalPartialHelp(t) getOrElse {
        // full check; we have to extend the model
      
        import TerForConvenience._
      
        getStatusHelp(false) match {
          
          //////////////////////////////////////////////////////////////////////

          case ProverStatus.Sat | ProverStatus.Invalid if (currentModel != null) => {
            // then we work with a countermodel of the constraints

            val p = new IExpression.Predicate("p", 1)
            implicit val extendedOrder = currentModel.order extendPred p

            val pAssertion =
              ReduceWithConjunction(currentModel, functionalPreds, extendedOrder)(
                toInternalNoAxioms(!IAtom(p, List(t)), extendedOrder))
            val extendedProver =
              currentProver.assert(currentModel, extendedOrder)
                           .conclude(pAssertion, extendedOrder)

            (extendedProver checkValidity true) match {
              case Left(m) if (!m.isFalse) => {
                val pAtoms = m.predConj.positiveLitsWithPred(p)
                //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
                Debug.assertInt(AC, pAtoms.size == 1 &&
                                    pAtoms.head.constants.isEmpty)
                //-END-ASSERTION-///////////////////////////////////////////////////////

                val pAtom = pAtoms.head
                val result = pAtom(0).constant
                currentModel = ReduceWithConjunction(conj(pAtom), extendedOrder)(m)
                lastPartialModel = null
              
                result
              }
              case _ =>
                throw new Exception ("Model extension failed.\n" +
                                     "This is probably caused by badly chosen triggers,\n" +
                                     "preventing complete application of axioms.")
            }
          }
        
          //////////////////////////////////////////////////////////////////////

          case ProverStatus.Unsat | ProverStatus.Valid if (currentModel != null) => {
            // then we work with a model of the existential constants 

            val c = new IExpression.ConstantTerm("c")
            implicit val extendedOrder = currentModel.order extend c

            val cAssertion =
              ReduceWithConjunction(currentModel, functionalPreds, extendedOrder)(
                toInternalNoAxioms(IExpression.i(c) =/= t, extendedOrder))
            val extendedProver =
              (ModelSearchProver emptyIncProver goalSettings
                       ).assert(currentModel, extendedOrder)
                        .conclude(cAssertion, extendedOrder)

            (extendedProver checkValidity true) match {
              case Left(m) if (!m.isFalse) => {
                val reduced = ReduceWithEqs(m.arithConj.positiveEqs, extendedOrder)(l(c))
                //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
                Debug.assertInt(AC, reduced.constants.isEmpty)
                //-END-ASSERTION-///////////////////////////////////////////////////////
                val result = reduced.constant
                currentModel = ConstantSubst(c, result, extendedOrder)(m)
                lastPartialModel = null
              
                result
              }
              case _ =>
                throw new Exception ("Model extension failed.\n" +
                                     "This is probably caused by badly chosen triggers,\n" +
                                     "preventing complete application of axioms.")
            }
          }
        
          //////////////////////////////////////////////////////////////////////

          case _ => {
            assert(false)
            null
          }
        }
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
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + evalPartial(")
      PrettyScalaLineariser(getFunctionNames)(t)
      println("))")
    }
    evalPartialHelp(t)
  }

  def evalPartialHelp(t : ITerm) : Option[IdealInt] = t match {
    case IConstant(c) =>
      // faster check, find an equation that determines the value of c
      evalPartialHelp(c)
    
    case t => {
      // more complex check by reducing the expression via the model

      val (reduced, _, _) = reduceTerm(t)
        
      if (reduced.isLiteral &&
          reduced.arithConj.positiveEqs.size == 1 &&
          reduced.constants.size == 1)
        Some(-reduced.arithConj.positiveEqs.head.constant)
      else
        None
    }
  }

  /**
   * Reduce the expression <code>t === c</code>, for some fresh constant
   * <code>c</code>.
   */
  private def reduceTerm(t : ITerm)
                        : (Conjunction, IExpression.ConstantTerm, TermOrder) = {
        import TerForConvenience._
        val existential = setupTermEval
        
        val c = new IExpression.ConstantTerm ("c")
        val extendedOrder = currentModel.order extend c
        
        val reduced =
          ReduceWithConjunction(currentModel, functionalPreds, extendedOrder)(
                                toInternalNoAxioms(t === c, extendedOrder))

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, !existential || (
          // in the existential case, the queried term should only contain
          // existential constants
          (reduced.constants subsetOf (existentialConstants + c)) &&
          reduced.predicates.isEmpty
          ))
        //-END-ASSERTION-///////////////////////////////////////////////////////

        (reduced, c, extendedOrder)
  }
  
  private def setupTermEval = getStatusHelp(false) match {
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
  
  /**
   * Evaluate the given symbol in the current model, returning <code>None</code>
   * in case the model does not completely determine the value of the symbol.
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
  def eval(c : IExpression.ConstantTerm) : IdealInt = {
    doDumpScala {
      println("println(\"" + getScalaNum + ": \" + eval(" + c + "))")
    }
    evalHelp(c)
  }

  private def evalHelp(c : IExpression.ConstantTerm) : IdealInt =
    evalPartialHelp(c) getOrElse {
      // then we have to extend the model
    
      if (!(currentOrder.orderedPredicates forall (_.arity == 0))) {
        // we assume 0 as default value, but have to store this value
        import TerForConvenience._
        implicit val o = currentModel.order
        currentModel = currentModel & (c === 0)
        lastPartialModel = null
      }
      
      IdealInt.ZERO
    }
  
  /**
   * Evaluate the given symbol in the current model, returning <code>None</code>
   * in case the model does not completely determine the value of the symbol.
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
  def evalPartial(c : IExpression.ConstantTerm) : Option[IdealInt] = {
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + evalPartial(" + c + "))")
    }
    evalPartialHelp(c)
  }

  private def evalPartialHelp(c : IExpression.ConstantTerm) : Option[IdealInt] = {
    val existential = setupTermEval
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, !existential || (existentialConstants contains c))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // find an equation that determines the value of c
        
    for (lc <- currentModel.arithConj.positiveEqs.toMap get c) yield -lc.constant
  }
  
  /**
   * Evaluate the given formula in the current model.
   * This method can only be called after receiving the result
   * <code>ProverStatus.Sat</code> or <code>ProverStates.Invalid</code>.
   */
  def eval(f : IFormula) : Boolean = {
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + eval(")
      PrettyScalaLineariser(getFunctionNames)(f)
      println("))")
    }

    evalPartialHelp(f) match {

      case Left(res) => res

      case Right(reducedF) => {
        // then we have to extend the model
  
        import TerForConvenience._
  
        f match {
          case f if (currentOrder.orderedPredicates forall (_.arity == 0)) => {
            // then we can just set default values for all irreducible constants
            // and Boolean variables
  
            //-BEGIN-ASSERTION-///////////////////////////////////////////////////
            Debug.assertInt(AC, Seqs.disjoint(reducedF.constants,
                                              currentModel.constants))
            //-END-ASSERTION-/////////////////////////////////////////////////////
  
            implicit val order =
              currentOrder
            val implicitAssumptions =
              (reducedF.constants.toSeq === 0) &
              conj(for (p <- reducedF.predicates.iterator)
                   yield Atom(p, List(), currentOrder))
            val reduced =
              ReduceWithConjunction(implicitAssumptions, currentOrder)(reducedF)
  
            //-BEGIN-ASSERTION-///////////////////////////////////////////////////
            Debug.assertInt(AC, reduced.isTrue || reduced.isFalse)
            //-END-ASSERTION-/////////////////////////////////////////////////////
  
            reduced.isTrue
          }
          
          case IAtom(p, Seq())
            if (proofActorStatus == ProofActorStatus.AtPartialModel) => {
            // then we will just extend the partial model with a default value
          
            implicit val order = currentModel.order
            val a = Atom(p, List(), order)
            currentModel = currentModel & a
            lastPartialModel = null
          
            true
          }
            
          case f => {
            val p = new IExpression.Predicate("p", 0)
            implicit val extendedOrder = currentModel.order extendPred p
            val pAssertion =
              ReduceWithConjunction(currentModel, functionalPreds, extendedOrder)(
                toInternalNoAxioms(IAtom(p, Seq()) </> f, extendedOrder))
            val extendedProver =
              currentProver.assert(currentModel, extendedOrder)
                           .conclude(pAssertion, extendedOrder)
  
            (extendedProver checkValidity true) match {
              case Left(m) if (!m.isFalse) => {
                val (reduced, _) = ReduceWithPredLits(m.predConj, Set(), extendedOrder)(p)
                //-BEGIN-ASSERTION-/////////////////////////////////////////////////
                Debug.assertInt(AC, reduced.isTrue || reduced.isFalse)
                //-END-ASSERTION-///////////////////////////////////////////////////
                val result = reduced.isTrue
                val pf : Conjunction = p
          
                currentModel = ReduceWithConjunction(if (result) pf else !pf, extendedOrder)(m)
                lastPartialModel = null        
  
                result
              }
              case _ =>
                throw new Exception ("Model extension failed.\n" +
                                     "This is probably caused by badly chosen triggers,\n" +
                                     "preventing complete application of axioms.")
            }
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
    doDumpScala {
      print("println(\"" + getScalaNum + ": \" + evalPartial(")
      PrettyScalaLineariser(getFunctionNames)(f)
      println("))")
    }

    evalPartialHelp(f) match {
      case Left(res) => Some(res)
      case Right(_) => None
    }
  }
  
  private def evalPartialHelp(f : IFormula) : Either[Boolean,Conjunction] = {
    import TerForConvenience._
    
    doDumpSMT {
      print("(get-value (")
      SMTLineariser(f)
      println("))")
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, Set(ProverStatus.Sat,
                            ProverStatus.Invalid) contains getStatusHelp(false))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    f match {
      case IAtom(p, args) if (args forall (_.isInstanceOf[IIntLit])) => {
        if (!args.isEmpty)
          ensureFullModel
        
        val a = Atom(p, for (IIntLit(value) <- args) yield l(value), currentOrder)
        
        if (currentModel.predConj.positiveLitsAsSet contains a)
          Left(true)
        else if (currentModel.predConj.negativeLitsAsSet contains a)
          Left(false)
        else
          Right(a)
      }
      case _ => {
        // more complex check by reducing the expression via the model
        ensureFullModel

        val reduced =
          ReduceWithConjunction(currentModel, functionalPreds, currentModel.order)(
                                  toInternalNoAxioms(f, currentOrder))

        if (reduced.isTrue)
          Left(true)
        else if (reduced.isFalse)
          Left(false)
        else
          Right(reduced)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Execute a computation within a local scope. After leaving the scope,
   * assertions and declarations done in the meantime will disappear.
   */
  def scope[A](comp: => A) : A = {
    push
    try {
      comp
    } finally {
      if (getStatusHelp(false) == ProverStatus.Running) {
        // then something really bad happened, and we are in an inconsistent
        // state
        proofActor ! ShutdownCommand
      } else {
        pop
      }
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
                       functionalPreds, functionEnc.clone,
                       arrayFuns, formulaeInProver,
                       currentPartitionNum,
                       constructProofs, mostGeneralConstraints,
                       validityMode, lastStatus,
                       currentModel, currentConstraint, currentCertificate,
                       theoryPlugin, theoryCollector.clone)
    
    doDumpSMT {
      println("(push 1)")
    }
    doDumpScala {
      println
      println("scope {")
    }
  }
  
  /**
   * Pop the top-most frame from the assertion stack.
   */
  def pop : Unit = {
    doDumpSMT {
      println("(pop 1)")
    }
    doDumpScala {
      println("} // pop scope")
      println
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, getStatusHelp(false) != ProverStatus.Running)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (oldPreprocSettings, oldProver, oldOrder, oldExConstants,
         oldFunctionalPreds, oldFunctionEnc, oldArrayFuns,
         oldFormulaeInProver, oldPartitionNum, oldConstructProofs,
         oldMGCs, oldValidityMode, oldStatus, oldModel, oldConstraint, oldCert,
         oldTheoryPlugin, oldTheories) =
      storedStates.pop
    preprocSettings = oldPreprocSettings
    currentProver = oldProver
    currentOrder = oldOrder
    existentialConstants = oldExConstants
    functionalPreds = oldFunctionalPreds
    functionEnc = oldFunctionEnc
    arrayFuns = oldArrayFuns
    formulaeInProver = oldFormulaeInProver
    currentPartitionNum = oldPartitionNum
    constructProofs = oldConstructProofs
    mostGeneralConstraints = oldMGCs
    formulaeTodo = false
    rawFormulaeTodo = LazyConjunction.FALSE
    validityMode = oldValidityMode
    lastStatus = oldStatus
    currentModel = oldModel
    decoderDataCache.clear
    lastPartialModel = null
    currentConstraint = oldConstraint
    currentCertificate = oldCert
    proofActorStatus = ProofActorStatus.Init
    theoryPlugin = oldTheoryPlugin
    theoryCollector = oldTheories 
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def flushTodo : Unit = {
    val (transTodo, axioms) = formulaeTodo match {
      case IBoolLit(false) => (Conjunction.FALSE, Conjunction.FALSE)
      case _ => toInternal(formulaeTodo)
    }
    formulaeTodo = false

    if (!transTodo.isFalse || !axioms.isFalse || !rawFormulaeTodo.isFalse) {
      implicit val o = currentOrder
      val completeFor =
        (rawFormulaeTodo | LazyConjunction(transTodo)).toConjunction

      val additionalAxioms =
        if (rawFormulaeTodo.isFalse) {
          Conjunction.FALSE
        } else {
          // check whether further theories have to be loaded for the asserted
          // raw formulae
          // TODO: this should be done in a more intelligent way, to try and
          // make the TermOrders match up in more cases

          theoryCollector(completeFor.order)
          val theoryAxioms = checkNewTheories
  
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
          Debug.assertInt(AC, currentOrder isSortingOf completeFor)
          //-END-ASSERTION-///////////////////////////////////////////////////////

          !Conjunction.conj(theoryAxioms, currentOrder)
        }

      rawFormulaeTodo = LazyConjunction.FALSE
      val reducedFor =
        ReduceWithConjunction(Conjunction.TRUE, functionalPreds, currentOrder)(
                              completeFor)
      addToProver(reducedFor,
                  Conjunction.disj(Array(axioms, additionalAxioms), currentOrder))
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
            restartProofActor
          }
      }
      
      if (currentProver != null) {
        if ((IterativeClauseMatcher.isMatchableRec(completeFor,
               Param.PREDICATE_MATCH_CONFIG(goalSettings))) &&
            Seqs.disjoint(completeFor.constants, existentialConstants))
          currentProver =
            currentProver.conclude(List(completeFor, axioms), currentOrder)
        else
          currentProver = null
      }
  }
  
  private def resetModel = {
    currentModel = null
    lastPartialModel = null
    currentConstraint = null
    currentCertificate = null
    lastStatus = ProverStatus.Unknown
    decoderDataCache.clear
  }
  
  private def addFormula(f : IFormula) : Unit = {
    resetModel
    doDumpSMT {
      f match {
        case INot(g) => {
          print("(assert ")
          SMTLineariser(g)
          println(")")
        }
        case f => {
          print("(assert (not ")
          SMTLineariser(f)
          println("))")
        }
      }
    }
    formulaeTodo = formulaeTodo | f
  }

  private def addFormula(f : LazyConjunction) : Unit = {
    resetModel
    doDumpSMT {
      print("; adding internal formula: " + f)
    }
    implicit val o = currentOrder
    rawFormulaeTodo = rawFormulaeTodo | f
  }

  private def toInternalNoAxioms(f : IFormula,
                                 order : TermOrder) : Conjunction = {
    val sig = Signature(Set(),
                        existentialConstants,
                        order.orderedConstants -- existentialConstants,
                        Map(), // TODO: also handle predicate_match_config
                        order,
                        theoryCollector.theories)
    val (fors, _, newSig) =
      Preprocessing(INamedPart(FormulaPart, f), List(), sig, preprocSettings, functionEnc)
    functionEnc.clearAxioms

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, order == newSig.order &&
                        !(fors exists { case INamedPart(PartName.NO_NAME, _) => true
                                        case _ => false }))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = 
      Conjunction.conj(InputAbsy2Internal(
        IExpression.or(for (INamedPart(FormulaPart, f) <- fors.iterator)
                       yield f), order), order)
    formula
  }

  private def toInternal(f : IFormula) : (Conjunction, Conjunction) = {
    // check whether theories are involved that we don't know yet
    theoryCollector(f)
    val theoryAxioms = checkNewTheories

    val sig = Signature(Set(),
                        existentialConstants,
                        currentOrder.orderedConstants -- existentialConstants,
                        Map(), // TODO: also handle predicate_match_config
                        currentOrder,
                        theoryCollector.theories)
    val (fors, _, newSig) =
      Preprocessing(INamedPart(FormulaPart, f), List(), sig, preprocSettings, functionEnc)
    functionEnc.clearAxioms

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, currentOrder == newSig.order &&
                  (functionEnc.predTranslation.keySet subsetOf functionalPreds))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = 
      Conjunction.conj(InputAbsy2Internal(
        IExpression.or(for (INamedPart(FormulaPart, f) <- fors.iterator)
                       yield f), currentOrder), currentOrder)
    val axioms = 
      Conjunction.disjFor(
        List(InputAbsy2Internal(
               IExpression.or(for (INamedPart(PartName.NO_NAME, f) <- fors.iterator)
                              yield f), currentOrder)) ++ theoryAxioms, currentOrder)
    (formula, axioms)
  }
  
  private def checkNewTheories : Seq[Conjunction] =
    if (theoryCollector.newTheories.isEmpty) {
      List()
    } else {
      val theoryAxioms =
        for (t <- theoryCollector.newTheories) yield {
          currentOrder = t extend currentOrder
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
          Debug.assertInt(AC, (currentOrder isSortingOf t.axioms) &&
                              (currentOrder isSortingOf t.totalityAxioms))
          //-END-ASSERTION-/////////////////////////////////////////////////////////
  
          functionEnc addTheory t
  
          // TODO: also handle predicate_match_config
  
          functionalPreds = functionalPreds ++ t.functionalPredicates
  
          for (plugin <- t.plugin) {
            //-BEGIN-ASSERTION-///////////////////////////////////////////////////
            // Multiple theory plugins are currently unsupported
            Debug.assertInt(AC, theoryPlugin == None)
            //-END-ASSERTION-/////////////////////////////////////////////////////
            theoryPlugin = Some(plugin)
          }
  
          Conjunction.negate(t.axioms, currentOrder)
        }

      theoryCollector.reset
      recreateProver

      theoryAxioms
    }

  private def goalSettings = {
    var gs = GoalSettings.DEFAULT
//    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
//    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    // currently done for all predicates encoding functions; should this be
    // restricted?
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, functionalPreds)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs = Param.THEORY_PLUGIN.set(gs, theoryPlugin)
    gs
  }

  private var preprocSettings : PreprocessingSettings = _
  private var currentOrder : TermOrder = _
  private var existentialConstants : Set[IExpression.ConstantTerm] = _
  private var functionalPreds : Set[IExpression.Predicate] = _
  private var functionEnc : FunctionEncoder = _
  private var currentProver : ModelSearchProver.IncProver = _
  private var currentModel : Conjunction = _
  private var lastPartialModel : PartialModel = null
  private var currentConstraint : Conjunction = _
  private var currentCertificate : Certificate = _
  private var formulaeInProver : List[(Int, Conjunction)] = List()
  private var currentPartitionNum : Int = -1
  private var constructProofs : Boolean = false
  private var mostGeneralConstraints : Boolean = false
  private var formulaeTodo : IFormula = false
  private var rawFormulaeTodo : LazyConjunction = LazyConjunction.FALSE
  private var theoryPlugin : Option[Plugin] = None
  private var theoryCollector : TheoryCollector = _

  private val storedStates = new ArrayStack[(PreprocessingSettings,
                                             ModelSearchProver.IncProver,
                                             TermOrder,
                                             Set[IExpression.ConstantTerm],
                                             Set[IExpression.Predicate],
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
                                             Certificate,
                                             Option[Plugin],
                                             TheoryCollector)]
  
  private def recreateProver = {
    preprocSettings =
      // TODO: correct setting even if Theories are used?
      Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
             preprocSettings, functionEnc.predTranslation.values.toSet)
    if (currentProver != null)
      currentProver = (ModelSearchProver emptyIncProver goalSettings)
                          .conclude(formulaeInProver.unzip._2, currentOrder)
    restartProofActor
  }
  
  private def restartProofActor =
    (proofActorStatus = ProofActorStatus.Init)
  
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
                 Conjunction.disj(forsToAdd, model.order))
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
      val select = createFunctionHelp("select" + arity, arity + 1)
      val store = createFunctionHelp("store" + arity, arity + 2)
      arrayFuns += (arity -> (select, store))
      
      val oldPartitionNum = currentPartitionNum
      setPartitionNumberHelp(-1)
      addFormula(!Parser2InputAbsy.arrayAxioms(arity, select, store))
      setPartitionNumberHelp(oldPartitionNum)
      
      (select, store)
    })
  
  private def getFunctionNames =
    (for ((_, (sel, sto)) <- arrayFuns.iterator;
          p <- Seqs.doubleIterator(sel -> "select", sto -> "store"))
     yield p).toMap

  //////////////////////////////////////////////////////////////////////////////

  reset

}
