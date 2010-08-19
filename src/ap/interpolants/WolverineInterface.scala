/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010 Philipp Ruemmer <ph_r@gmx.net>
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
import scala.collection.mutable.ArrayBuffer

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.TerForConvenience._
import ap.util.{Debug, Seqs}

object WolverineInterfaceMain extends {

  val nothing =
    Console.withOut(Console.err) {
      CmdlMain.printGreeting
      println
      println("(The Princess in the wolf skin)")
      println
    }

} with SoftwareInterpolationFramework {
  
  private val AC = Debug.AC_MAIN

  private var assertions = true
  
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
  
  Debug.enabledAssertions.value_= {
    // we do our own implication checks in this class
    case (_, Debug.AC_INTERPOLATION_IMPLICATION_CHECKS) => false
    case _ => assertions
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val wolverineLineariser = new WolverineInterpolantLineariser
  
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
        parseAndSimplify(new java.io.BufferedReader (
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

  private def doInterpolation(transitionParts : Map[PartName, Conjunction],
                              sig : Signature) : Unit = {
    val names = sortNamesLex(transitionParts)
    val parts = for (n <- names) yield transitionParts(n)

    val res =
      genInterpolants(parts,
                      transitionParts.getOrElse(PartName.NO_NAME, Conjunction.TRUE),
                      sig.order)
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
            
            val simpInter = toInputAbsyAndSimplify(i)

            /* Console.withOut(Console.err) {
              println("Raw interpolant:        " + i)
              println("Simplified interpolant: " + simpInter)
          } */
    
            wolverineLineariser.visit(simpInter, List())
            println
    
            //-BEGIN-ASSERTION-///////////////////////////////////////////
            // Check that the implications I_i & T_(i+1) => I_(i+1) hold,
            // where T_i are the transition relations and I_i the generated
            // interpolants
            Debug.assertIntFast(AC, {
              val (implication, order) =
                toInternal(lastInterpolant ==> simpInter, sig)
    
              interpolantImpChecker.conclude(transitionParts(names(num)), order)
                                   .conclude(implication, order)
                                   .checkValidity(false) == Left(Conjunction.FALSE)
            })
            
            lastInterpolant = simpInter
            //-END-ASSERTION-/////////////////////////////////////////////
          }
        }
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def doCheckValidity(transitionParts : Map[PartName, Conjunction],
                              sig : Signature) : Unit = {
    val res = validityCheckProver.conclude(transitionParts.values.toList, sig.order)
                                 .checkValidity(false)
    
    Console.withOut(java.lang.System.out) {
      res match {
        case Left(Conjunction.FALSE) =>
          println("VALID")
        case Left(counterexample) => {
          println("INVALID")
          println(counterexample)
        }
        case _ => assert(false)
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

class WolverineInterpolantLineariser extends CollectingVisitor[List[String], Unit] {

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
