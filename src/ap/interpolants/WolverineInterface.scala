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
import ap.terfor.{Formula, Term, OneTerm, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
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
  
  private val preprocSettings = PreprocessingSettings.DEFAULT
  private val goalSettings = Param.PROOF_CONSTRUCTION.set(GoalSettings.DEFAULT, true)
  
  private val preludeEnv = new Environment
  private val functionEncoder = new FunctionEncoder
  
  private val (backgroundPred, preludeOrder) = Console.withOut(Console.err) {
    print("Reading prelude ... ")
    val reader = ResourceFiles.preludeReader
    val (iBackgroundPredRaw, _, signature) = Parser2InputAbsy(reader, preludeEnv)
    reader.close

    val (iBackgroundFors, _, signature2) =
      Preprocessing(iBackgroundPredRaw, List(), signature,
                    preprocSettings, functionEncoder)
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
              Console.withOut(Console.err) {
                println(i)
              }
              
              //////////////////////////////////////////////////////////////////
              Debug.assertInt(AC, i.predicates.isEmpty)
              //////////////////////////////////////////////////////////////////
              
/*              val predFreeI =
                if (i.predicates.isEmpty)
                  i
                else
                  PresburgerTools.eliminatePredicates(i, !backgroundPred) */
              
              println(WolverineInterpolantLineariser(i))
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

    lazy val namedParts =
      Map() ++ (for (INamedPart(name, f) <- iProblemParts)
                yield (name -> conj(InputAbsy2Internal(f, order))))

    println("Parsed problem")

    (namedParts, signature2)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def genInterpolants(namedParts : Map[PartName, Conjunction],
                              sig : Signature)
                             : Either[Conjunction, Iterator[Conjunction]] = {
    val names = Seqs.toArray((Set() ++ namedParts.keys) - PartName.NO_NAME)
    Sorting.stableSort(names, (x : PartName, y : PartName) => x.toString < y.toString)
    
    val inputFors = (for (n <- names) yield namedParts(n)) ++ List(backgroundPred)
    
//    ap.util.Timer.measure("solving") {
      ModelSearchProver(inputFors, sig.order, goalSettings)
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
                                        interspec)
//            ap.util.Timer.measure("interpolating") {
                Interpolator(cert, iContext)
//            }
          })
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

object WolverineInterpolantLineariser {

  private val AC = Debug.AC_MAIN

  private def binOp(emptyOp : String, binOp : String, args : Iterator[String])
                   : String =
    if (args.hasNext)
      args.reduceLeft[String]({
        case (f1 : String, f2 : String) => "(" + binOp + " " + f1 + " " + f2 + ")"
      })
    else
      emptyOp
  
  private def linConj(fors : Iterator[String]) : String =
    binOp("(true)", "&", for (f <- fors; if (f != "(true)")) yield f)

  private def neg(f : String) : String = f match {
    case "(true)" => "(false)"
    case "(false)" => "(true)"
    case f => "(! " + f + ")"
  }
  
  private def linCoeffTerm(p : (IdealInt, Term)) : String = p match {
    case (c, OneTerm) => "(lit " + c.toString + ")"
    case (IdealInt.ONE, t) => "(sym " + t.toString + ")"
    case (c, t) => "(* (lit " + c.toString + ") (sym " + t.toString + "))"
  }
  
  private def linEq(op : String, eq : LinearCombination) : String = eq match {
    case Seq() =>
      "(true)"
    case Seq(p @ (c, t)) if (c.signum >= 0) =>
      "(" + op + " " + linCoeffTerm(p) + " (lit 0))"
    case Seq(p @ (c, t)) if (c.signum < 0) =>
      "(" + op + " (lit 0) " + linCoeffTerm((-c, t)) + ")"
    case Seq(p1 @ (c1, t1), (c2, t2)) if (c1.signum >= 0 && c2.signum < 0) =>
      "(" + op + " " + linCoeffTerm(p1) + " " + linCoeffTerm((-c2, t2)) + ")"
    case Seq((c2, t2), p1 @ (c1, t1)) if (c1.signum >= 0 && c2.signum < 0) =>
      "(" + op + " " + linCoeffTerm(p1) + " " + linCoeffTerm((-c2, t2)) + ")"
    case seq =>
      "(" + op + " " +
        binOp("", "+",
              for (p <- seq.elements) yield linCoeffTerm(p)) + " (lit 0))"
  }
  
  private def lin(eqs : EquationConj) : String =
    linConj(for (eq <- eqs.elements) yield linEq("=", eq))

  private def lin(eqs : NegEquationConj) : String =
    linConj(for (eq <- eqs.elements) yield neg(linEq("=", eq)))

  private def lin(inEqs : InEqConj) : String =
    linConj(for (eq <- inEqs.elements) yield linEq(">=", eq))

  private def lin(ac : ArithConj) : String =
    if(ac.isFalse) "(false)" else
    linConj(List(lin(ac.positiveEqs), lin(ac.negativeEqs), lin(ac.inEqs)).elements)
  
  def apply(conj : Conjunction) : String = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC, conj.predConj.isTrue)
    ////////////////////////////////////////////////////////////////////////////
  
    if (conj.isDivisibility) {
      assert(false) // todo
      ""
    } else if (conj.isNonDivisibility) {
      assert(false) // todo
      ""
    } else {
      //////////////////////////////////////////////////////////////////////////
      Debug.assertPre(AC, conj.quans.isEmpty && 
                          conj.predConj.positiveLits.isEmpty && 
                          conj.predConj.negativeLits.isEmpty)
      //////////////////////////////////////////////////////////////////////////
      linConj(Iterator.single(lin(conj.arithConj)) ++
              (for (c <- conj.negatedConjs.elements) yield neg(apply(c))))
    }
  }
  
}