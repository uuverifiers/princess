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
  
  Debug.enableAllAssertions(false)
  
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
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val wolverineLineariser =
    new WolverineInterpolantLineariser(select, store)
  
  private val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def main(args: Array[String]) : Unit = Console.withOut(Console.err) {
    println
    println("Waiting for input ...")
    println("-> Terminate each interpolation problem with a \".\" in a separate line")
    println("-> Stop Princess with a \"quit\" in a separate line")

    while (true) {
      val stdinOutputStream = new java.io.PipedOutputStream
      val stdinInputStream = new java.io.PipedInputStream(stdinOutputStream)

      actor {
        // Read from the standard input in a separate thread, so that
        // parsing can start simultaneously
        try {
          var line = Console.in.readLine
          Console.withOut(stdinOutputStream) {
            while (line != ".") {
              if (line == null || line == "quit")
                java.lang.System.exit(0);
              println(line)
              line = Console.in.readLine
            }
          }
        } catch {
          case e : java.io.IOException => {
            println(e.getMessage)
            java.lang.System.exit(1)
          }
        }
        stdinOutputStream.close
      }
    
      val (namedParts, sig) =
        parseProblem(new java.io.BufferedReader (
                     new java.io.InputStreamReader(stdinInputStream)))

      val res = genInterpolants(namedParts, sig)
      Console.withOut(java.lang.System.out) {
        res match {
          case Left(counterexample) => {
            println("INVALID")
            println(counterexample)
          }
          case Right(interpolants) => {
            println("VALID")
            for (i <- interpolants) {
/*              val predFreeI =
                if (i.predicates.isEmpty)
                  i
                else
                  PresburgerTools.eliminatePredicates(i, !backgroundPred) */
              
//              println(WolverineInterpolantLineariser(i))
              
              val internalInter = Internal2InputAbsy(i, functionEncoder.predTranslation)
              val simpInter = Simplifier(internalInter)
/*              Console.withOut(Console.err) {
                  println(simpInter)
                } */
              
              wolverineLineariser.visit(simpInter, List())
              println
            }
          }
        }
        println(".")
        
/*        Console.withOut(Console.err) {
          println
          println(ap.util.Timer)
          ap.util.Timer.reset
          } */
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

  private def genInterpolants(namedParts : Map[PartName, Conjunction],
                              sig : Signature)
                             : Either[Conjunction, Iterator[Conjunction]] = {
    val names = Seqs.toArray((Set() ++ namedParts.keys) - PartName.NO_NAME)
    Sorting.stableSort(names, (x : PartName, y : PartName) => x.toString < y.toString)

//    ap.util.Timer.measure("solving") {
       interpolationProver.conclude((for (n <- names) yield namedParts(n)) ++
                                      (namedParts get PartName.NO_NAME).toList,
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
              new InterpolationContext (namedParts + (PartName.NO_NAME -> backgroundPred),
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
  
  /**
   * Rewrite a term to the form <code>coeff * symbol + remainder</code>
   * (where remainder does not contain the atomic term
   * <code>symbol</code>) and determine the coefficient and the remainder
   */
  private case class Sum(symbol : ITerm) {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC, symbol.isInstanceOf[IVariable] || symbol.isInstanceOf[IConstant])
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    def unapply(t : ITerm) : Option[(IdealInt, ITerm)] ={
      val (coeff, remainder) = decompose(t, 1)
      symbol match {
        case symbol : IVariable
          if ((SymbolCollector variables remainder) contains symbol) => None
        case IConstant(c)
          if ((SymbolCollector constants remainder) contains c) => None
        case _ => Some(coeff, remainder)
      }
    }

    private def decompose(t : ITerm,
                          coeff : IdealInt) : (IdealInt, ITerm) = t match {
      case `symbol` => (coeff, 0)
      case ITimes(c, t) => decompose(t, coeff * c)
      case IPlus(a, b) => {
        val (ca, ra) = decompose(a, coeff)
        val (cb, rb) = decompose(b, coeff)
        (ca + cb, ra +++ rb)
      }
      case _ => (0, t *** coeff)
    }
  }
  
  private val Var0Plus = Sum(IVariable(0))
  
  override def preVisit(t : IExpression, boundVars : List[String]) : PreVisitResult = {
    print("(")
    t match {
      // we do some special rewriting for the theory of arrays (to avoid
      // quantifiers if possible)
      // TODO: generalise this
      
      case IQuantified(Quantifier.EX, IIntFormula(EqZero,
                 Difference(IFunApp(store, Seq(IVariable(0), t1, t2)), t3))) => {
        print("= ")
        visit(select(t3, t1), "" :: boundVars)
        visit(t2, "" :: boundVars)
        print(") ")
        ShortCutResult()
      }

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
