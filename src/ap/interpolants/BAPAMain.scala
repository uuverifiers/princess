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

object BAPAMain extends {

  val nothing =
    Console.withOut(Console.err) {
      CmdlMain.printGreeting
      println
      println("(BAPA version)")
      println
    }

} with BAPAFramework {
  
  private val AC = Debug.AC_BAPA

  private var assertions = true
  
  import IExpression._
  
  java.lang.System getenv "BAPA_PRINCESS_OPTIONS" match {
    case null => // nothing
    case str => {
//      val DumpInterpolationProblems = """dumpInterpolationProblems=(.+)""".r
      
      for (option <- str split ',') option match {
        case "noAssertions" =>
          assertions = false
//        case DumpInterpolationProblems(filename) =>
//          interpolationProblemBasename = filename
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
    case (_, Debug.AC_INTERPOLATION_IMPLICATION_CHECKS) => assertions
    case _ => assertions
  }
  
  //////////////////////////////////////////////////////////////////////////////

//  private val wolverineLineariser = new WolverineInterpolantLineariser
  
  //////////////////////////////////////////////////////////////////////////////

  private val baseConstants = preludeSignature.nullaryFunctions
  
  def main(args: Array[String]) : Unit = Console.withOut(Console.err) {
    println
    println("Waiting for input ...")
    println("-> Terminate each problem with \"interpolate.\" or \"checkValidity.\"")
    println("   in a separate line")
    println("-> Specify options using the environment variable \"BAPA_PRINCESS_OPTIONS\"")
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

      val (problem, sig) =
        parseProblem(new java.io.BufferedReader (
                     new java.io.InputStreamReader(stdinInputStream)))
                     
      receive {
        case "interpolate."   => doInterpolation(problem, sig)
        case "checkValidity." => docheckValidity(problem, sig)
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

  private def doInterpolation(problem : IFormula, sig : Signature) : Unit = {
    // determine the part names and sort them lexicographically
    
    val fors = PartExtractor(problem)
    val names =
      (for (INamedPart(n, _) <- fors) yield n).sortWith(_.toString < _.toString)
    val intSpecs =
      for (i <- List.range(1, names.size)) yield IInterpolantSpec(names take i, names drop i)

    Console.withOut(java.lang.System.out) {
      interpolate(!problem,
                  sig.order sort (sig.nullaryFunctions -- baseConstants),
                  intSpecs) match {
        case None => {
          println("INVALID")
        }
        case Some(interpolants) => {
          println("VALID")
          
          //-BEGIN-ASSERTION-/////////////////////////////////////////////
          // used for assertions: interpolants imply each other
          val forsSorted =
            for (n <- names) yield connect(
              for (INamedPart(`n`, f) <- fors) yield f, IBinJunctor.Or)
          var lastInterpolant : IFormula = true
          val interpolantImpChecker = satCheckProver
//            satCheckProver.conclude((transitionParts get PartName.NO_NAME).toList,
//                                    sig.order)
          //-END-ASSERTION-///////////////////////////////////////////////
          
//          dumpInterpolationProblem(transitionParts, sig)

          for ((i, num) <- interpolants.zipWithIndex) {

//            wolverineLineariser.visit(simpInter, List())
//            println
  
            println(i)
            
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            // Check that the implications I_i & T_(i+1) => I_(i+1) hold,
            // where T_i are the transition relations and I_i the generated
            // interpolants
            Debug.assertIntFast(AC, {
              val iImp = lastInterpolant ==> (i | forsSorted(num))
              val (implication, order) = toInternal(iImp, sig)
              interpolantImpChecker.conclude(implication, order)
                                   .checkValidity(false) == Left(Conjunction.FALSE)
            })
            
            lastInterpolant = i
            //-END-ASSERTION-///////////////////////////////////////////////////
          }
          
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // Last interpolant should be inconsistent with last transition
          // relation
          Debug.assertIntFast(AC, {
            val iImp = lastInterpolant ==> forsSorted.last
            val (implication, order) = toInternal(iImp, sig)
            interpolantImpChecker.conclude(implication, order)
                                 .checkValidity(false) == Left(Conjunction.FALSE)
          })
          //-END-ASSERTION-/////////////////////////////////////////////
        }
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def docheckValidity(problem : IFormula, sig : Signature) : Unit =
    Console.withOut(java.lang.System.out) {
      if (isSat(!problem, sig.order sort (sig.nullaryFunctions -- baseConstants)))
        println("INVALID")
      else
        println("VALID")
    }
}
