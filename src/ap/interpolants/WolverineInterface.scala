/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.util.Sorting

import ap.basetypes.IdealInt
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.TerForConvenience._
import ap.proof.ModelSearchProver
import ap.util.{Debug, Seqs}

object ResourceFiles {

  private val preludeFile = "wolverine_resources/prelude.pri"
//  private val commOpsFile = "/resources/commutativeOperators.list"

  private def toReader(stream : java.io.InputStream) =
    new java.io.BufferedReader (new java.io.InputStreamReader(stream))

  private def resourceAsStream(filename : String) =
//    ResourceFiles.getClass.getResourceAsStream(filename)
    new java.io.FileInputStream(filename)
  
  def preludeReader = toReader(resourceAsStream(preludeFile))
//  def commOpsReader = toReader(resourceAsStream(commOpsFile))
}

////////////////////////////////////////////////////////////////////////////////

object WolverineInterfaceMain {
  
  private val AC = Debug.AC_MAIN

  private var assertions = true
  private var interpolationProblemBasename = ""
  private var interpolationProblemNum = 0
  
  java.lang.System getenv "WERE_PRINCESS_OPTIONS" match {
    case null => // nothing
    case str => {
      val DumpInterpolationProblems = """dumpInterpolationProblems=(.+)""".r
      
      for (option <- str split ',') option match {
        case "noAssertions" =>
          assertions = false
        case DumpInterpolationProblems(filename) =>
          interpolationProblemBasename = filename
        case x => Console.withOut(Console.err) {
          println("Unknown option: " + x)
          println("Possible options are: noAssertions")
          java.lang.System.exit(1)
        }
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  Debug.enabledAssertions = {
    // we do our own implication checks in this class
    case (_, Debug.AC_INTERPOLATION_IMPLICATION_CHECKS) => false
    case _ => assertions
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  Console.withOut(Console.err) {
    CmdlMain.printGreeting
    println
    println("(The Princess in the wolf skin)")
    println
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val preludeEnv = new Environment
  private val functionEncoder = new FunctionEncoder
  
  private val (backgroundPred, preludeOrder) = Console.withOut(Console.err) {
    print("Reading prelude ... ")
    val reader = ResourceFiles.preludeReader
    val (iBackgroundPredRaw, _, signature) = Parser2InputAbsy(reader, preludeEnv)
    reader.close

    val (iBackgroundFors, _, signature2) =
      Preprocessing(iBackgroundPredRaw, List(), signature,
                    PreprocessingSettings.DEFAULT, functionEncoder)
    functionEncoder.clearAxioms
    
    val iBackgroundPred =
      IExpression.connect(for (INamedPart(_, f) <- iBackgroundFors.elements)
                            yield f,
                          IBinJunctor.Or)
    implicit val order = signature2.order
    
    val res = InputAbsy2Internal(iBackgroundPred, order)
    
    // we put the (possibly extended) order back into the environment, so that
    // we can continue parsing the transition relations with it
    preludeEnv.order = order

    val reducedRes = ReduceWithConjunction(Conjunction.TRUE, order)(conj(res))
    
    println("done")
    (reducedRes, order)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private val select =
    preludeEnv.lookupSym("select") match {
      case Environment.Function(f) => f
      case _ => throw new Error("Expected select to be defined as a function");
    }
  
  private val store = 
    preludeEnv.lookupSym("store") match {
      case Environment.Function(f) => f
      case _ => throw new Error("Expected store to be defined as a function");
    }
  
  //////////////////////////////////////////////////////////////////////////////

  private val preprocSettings =
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(PreprocessingSettings.DEFAULT,
                                                     Set(select, store))
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(GoalSettings.DEFAULT, true)
  private val validityCheckSettings =
    GoalSettings.DEFAULT
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val wolverineLineariser =
    new WolverineInterpolantLineariser(select, store)
  
  private lazy val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  private lazy val validityCheckProver = {
    val prover = ModelSearchProver emptyIncProver validityCheckSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val simplifier = new WolverineSimplifier (select, store)
  
  //////////////////////////////////////////////////////////////////////////////

  def main(args: Array[String]) : Unit = Console.withOut(Console.err) {
    println
    println("Waiting for input ...")
    println("-> Terminate each problem with \"interpolate.\" or \"checkValidity.\"")
    println("   in a separate line")
    println("-> Specify options using the environment variable \"WERE_PRINCESS_OPTIONS\"")
    println("-> Stop Princess with a \"quit.\" in a separate line")

    val mainActor = Actor.self
    
    while (true) {
      val stdinOutputStream = new java.io.PipedOutputStream
      val stdinInputStream = new java.io.PipedInputStream(stdinOutputStream)

      actor {
        // Read from the standard input in a separate thread, so that
        // parsing can start simultaneously
        try {
          var line = Console.in.readLine
          Console.withOut(stdinOutputStream) {
            while (line != null && !(line endsWith ".")) {
              println(line)
              line = Console.in.readLine
            }
          }
          
          line match {
            case null | "quit." => java.lang.System.exit(0);
            case _              => mainActor ! line
          }
        } catch {
          case e : java.io.IOException => {
            println(e.getMessage)
            java.lang.System.exit(1)
          }
        }
        stdinOutputStream.close
      }

      val (transitionParts, sig) =
        parseProblem(new java.io.BufferedReader (
                     new java.io.InputStreamReader(stdinInputStream)))

      receive {
        case "interpolate."   => doInterpolation(transitionParts, sig)
        case "checkValidity." => doCheckValidity(transitionParts, sig)
        case x : String       => {
          println("Unknown command: " + x)
          java.lang.System.exit(1)
        }
      }
      
      Console.withOut(java.lang.System.out) {
        println(".")
      }

/*      Console.withOut(Console.err) {
          println
          println(ap.util.Timer)
//          ap.util.Timer.reset
        } */
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def dumpInterpolationProblem(transitionParts : Map[PartName, Conjunction],
               	                       sig : Signature) : Unit =
    if (interpolationProblemBasename == "") {
      // nothing to do
    } else {
      import IExpression._
    
      val simpParts =
        for (n <- (if (transitionParts contains PartName.NO_NAME)
                     List(PartName.NO_NAME)
                   else
                     List()) ++
                   sortNames(transitionParts)) yield {
        val f = !transitionParts(n)
        val sf = PresburgerTools.eliminatePredicates(f, !backgroundPred, sig.order)
        INamedPart(n, Internal2InputAbsy(sf, Map()))
      }

      val filename = interpolationProblemBasename + interpolationProblemNum + ".pri"
      interpolationProblemNum = interpolationProblemNum + 1
      
      Console.withOut(new java.io.FileOutputStream(filename)) {
        PrincessLineariser(!connect(simpParts, IBinJunctor.And),
                           sig updateOrder sig.order.resetPredicates)
      }
    }
  
  //////////////////////////////////////////////////////////////////////////////

  private def doInterpolation(transitionParts : Map[PartName, Conjunction],
                              sig : Signature) : Unit = {
    val names = sortNames(transitionParts)

    val res = genInterpolants(names, transitionParts, sig)
    Console.withOut(java.lang.System.out) {
      res match {
        case Left(counterexample) => {
          println("INVALID")
          println(counterexample)
        }
        case Right(interpolants) => {
          println("VALID")
          
          //-BEGIN-ASSERTION-/////////////////////////////////////////////
          // used for assertions: interpolants imply each other
          var lastInterpolant : IFormula = true
          val interpolantImpChecker =
            validityCheckProver.conclude((transitionParts get
                                            PartName.NO_NAME).toList,
                                         sig.order)
          //-END-ASSERTION-///////////////////////////////////////////////
          
          dumpInterpolationProblem(transitionParts, sig)

          for ((i, num) <- interpolants.zipWithIndex) {
/*          val predFreeI =
              if (i.predicates.isEmpty)
                i
              else
                PresburgerTools.eliminatePredicates(i, !backgroundPred) */
            
            val internalInter =
              Internal2InputAbsy(i, functionEncoder.predTranslation)
            val simpInter =
//              ap.util.Timer.measure("simplifying") {
                simplifier(internalInter)
//              }

     /*       Console.withOut(Console.err) {
                println(simpInter)
     } */
    
            wolverineLineariser.visit(simpInter, List())
            println
    
            //-BEGIN-ASSERTION-///////////////////////////////////////////
            // Check that the implications I_i & T_(i+1) => I_(i+1) hold,
            // where T_i are the transition relations and I_i the generated
            // interpolants
            Debug.assertIntFast(AC, {
              val implication = lastInterpolant ==> simpInter
              
              val (interParts, _, sig2) =
                Preprocessing(implication, List(), sig,
                              preprocSettings, functionEncoder)
              functionEncoder.clearAxioms
              implicit val order = sig2.order
    
              val internalInterParts =
                for (INamedPart(_, f) <- interParts)
                  yield conj(InputAbsy2Internal(f, order))
    
              interpolantImpChecker.conclude(transitionParts(names(num)), order)
                                   .conclude(internalInterParts, order)
                                   .checkValidity == Left(Conjunction.FALSE)
            })
            
            lastInterpolant = simpInter
            //-END-ASSERTION-/////////////////////////////////////////////
          }
        }
      }
    }
  }
  
  private def sortNames(transitionParts : Map[PartName, Conjunction]) : Seq[PartName] = {
    val names = Seqs.toArray((Set() ++ transitionParts.keys) - PartName.NO_NAME)
    Sorting.stableSort(names, (x : PartName, y : PartName) => x.toString < y.toString)
    names
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def doCheckValidity(transitionParts : Map[PartName, Conjunction],
                              sig : Signature) : Unit = {
    val res =
      validityCheckProver.conclude(transitionParts.values.toList, sig.order)
                         .checkValidity
    
    Console.withOut(java.lang.System.out) {
      res match {
        case Left(Conjunction.FALSE) =>
          println("VALID")
        case Left(counterexample) => {
          println("INVALID")
          println(counterexample)
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def parseProblem(reader : java.io.Reader) = {
    val env = preludeEnv.clone
    val (problem, _, signature) = Parser2InputAbsy(reader, env)

    implicit val order = env.order

    val (iProblemParts, _, signature2) =
      Preprocessing(problem, List(), signature, preprocSettings, functionEncoder)
    functionEncoder.clearAxioms

    val namedParts =
      Map() ++ (for (INamedPart(name, f) <- iProblemParts)
                yield (name -> conj(InputAbsy2Internal(f, signature2.order))))

    // println("Parsed problem")

    (namedParts, signature2)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def genInterpolants(names : Seq[PartName],
                              transitionParts : Map[PartName, Conjunction],
                              sig : Signature)
                             : Either[Conjunction, Iterator[Conjunction]] = {
//    ap.util.Timer.measure("solving") {
       interpolationProver.conclude((for (n <- names) yield transitionParts(n)) ++
                                      (transitionParts get PartName.NO_NAME).toList,
                                    sig.order)
                          .checkValidity
//    }
    match {
      case Left(counterexample) =>
        Left(counterexample)
      case Right(cert) => {
        println("Found proof (size " + cert.inferenceCount + ")")

        Right(
          for (i <- Iterator.range(1, names.size)) yield {
            val interspec =
              IInterpolantSpec((names take i).toList, (names drop i).toList)
            val iContext =
              new InterpolationContext (transitionParts + (PartName.NO_NAME -> backgroundPred),
                                        interspec, cert.order)
//            ap.util.Timer.measure("interpolating") {
              Interpolator(cert, iContext)
//            }
          })
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions
 */
class WolverineSimplifier(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private class StoreRewriter(depth : Int) {
    var foundProblem : Boolean = false
    var storeArgs : Option[(ITerm, ITerm)] = None

    def rewrite(t : ITerm) : ITerm = t match {
      case IPlus(t1, t2) => rewrite(t1) +++ rewrite(t2)
      case IFunApp(`store`, Seq(IVariable(`depth`), t1, t2)) => {
        if (storeArgs != None)
          foundProblem = true
        storeArgs = Some(shiftVariables(t1), shiftVariables(t2))
        0
      }
      case _ => shiftVariables(t)
    }
    
    private def shiftVariables(t : ITerm) : ITerm = {
      if ((SymbolCollector variables t) contains IVariable(depth))
        foundProblem = true
      VariableShiftVisitor(t, depth + 1, -1)
    }
  }
  
  private def rewriteEquation(t : ITerm, depth : Int) : Option[IFormula] = {
    val rewriter = new StoreRewriter(depth)
    val newT = rewriter rewrite t

    rewriter.storeArgs match {
      case Some((t1, t2)) if (!rewriter.foundProblem) =>
        Some(select(newT, t1) === t2)
      case _ =>
        None
    }
  }
  
  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = f match {
      
    case IQuantified(q, subF) if (q == (if (negated) ALL else EX)) =>
      for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
        
    case IIntFormula(EqZero, t) if (!negated) =>
      rewriteEquation(t, depth)
    
    case INot(IIntFormula(EqZero, t)) if (negated) =>
      for (f <- rewriteEquation(t, depth)) yield !f
        
    case _ => None
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>  translate(f, false, 0) getOrElse expr
    case IQuantified(ALL, f) => translate(f, true, 0) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}

////////////////////////////////////////////////////////////////////////////////

class WolverineInterpolantLineariser(select : IFunction, store : IFunction)
      extends CollectingVisitor[List[String], Unit] {

  import IExpression._
  import IBinJunctor._
  import IIntRelation._
  
  private val AC = Debug.AC_MAIN

  private def printOp(op : String) : PreVisitResult = {
    print(op)
    print(" ")
    KeepArg
  }
  
  private object Difference {
    def unapply(t : IExpression) : Option[(ITerm, ITerm)] = t match {
      case ITimes(IdealInt.MINUS_ONE, t) => Some(0, t)
      case IPlus(t1, ITimes(IdealInt.MINUS_ONE, t2)) => Some(t1, t2)
      case IPlus(ITimes(IdealInt.MINUS_ONE, t2), t1) => Some(t1, t2)
      case IPlus(t, IIntLit(c)) => Some(t, -c)
      case IPlus(IIntLit(c), t) => Some(t, -c)
      case _ => None
    }
  }
  
  private val Var0Plus = SymbolSum(IVariable(0))
  
  override def preVisit(t : IExpression, boundVars : List[String]) : PreVisitResult = {
    print("(")
    t match {
      // divisibility constraints
      case IQuantified(Quantifier.EX,
                       IIntFormula(EqZero, Var0Plus(c, t))) => {
        print("divides "); print(c); print(" ")
        visit(t, "" :: boundVars)
        print(") ")
        ShortCutResult()
      }

      case IQuantified(Quantifier.ALL,
                       INot(IIntFormula(EqZero, Var0Plus(c, t)))) => {
        print("! (divides "); print(c); print(" ")
        visit(t, "" :: boundVars)
        print(")) ")
        ShortCutResult()
      }

      case _ : IIntLit =>                 printOp("lit")
      case _ : IConstant =>               printOp("sym")
      case _ : IVariable =>               printOp("boundVar")
      case ITimes(c, _) => {
        print("* (lit "); print(c); print(") ")
        KeepArg
      }
      case _ : IPlus =>                   printOp("+")
      
      case IFunApp(f, _) =>               printOp(f.name)
      
      case _ : INot =>                    printOp("!")
      case IBinFormula(And, _, _) =>      printOp("&")
      case IBinFormula(Or, _, _) =>       printOp("|")
      case _ : IAtom =>                   { assert(false); KeepArg } // TODO
      
      case IIntFormula(j, t) => {
    	printOp(j match {
                  case EqZero => "="
                  case GeqZero => ">="
                })
     
        t match {
          case Difference(t1, t2) => {
            visit(t1, boundVars); visit(t2, boundVars)
            print(") ")
            ShortCutResult()
          }
          case _ => KeepArg
        }
      }
      
      case IQuantified(q, _) => {
        printOp(q match {
                  case Quantifier.ALL => "forall"
                  case Quantifier.EX => "exists"
                })
        UniSubArgs(("x" + boundVars.size) :: boundVars)
      }
      
      case _ : ITrigger | _ : INamedPart => { assert(false); KeepArg } // Oops
      
      case _ => KeepArg // nothing
    }
  }
  
  def postVisit(t : IExpression, boundVars : List[String], subres : Seq[Unit]) : Unit = {
    t match {
      case IIntLit(value) =>     print(value)
      case IConstant(c) =>       print(c)
      case IVariable(index) =>   print(boundVars(index))

      case IBoolLit(value) =>    print(value)
      case _ : IIntFormula =>    print("(lit 0)")
      
      case _ => // nothing
    }
    print(") ")
  }
  
}
