/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.interpolants;

import ap.proof.ConstraintSimplifier
import ap.proof.tree.ProofTree
import ap.parameters.{GlobalSettings, GoalSettings, Param}
import ap.parser.{SMTLineariser, IExpression, IBinJunctor}
import ap.util.{Debug, Seqs}

object CmdlMain {

  def printGreeting = {
    println("________       _____")                                 
    println("___  __ \\_________(_)________________________________")
    println("__  /_/ /_  ___/_  /__  __ \\  ___/  _ \\_  ___/_  ___/")
    println("_  ____/_  /   _  / _  / / / /__ /  __/(__  )_(__  )")
    println("/_/     /_/    /_/  /_/ /_/\\___/ \\___//____/ /____/")  
  }
  
  def printUsage = {
    println("Usage: princess <option>* <inputfile>*")
    println
    printOptions
  }
  
  def printOptions = {
    println("Options:")
    println("  [+-]logo                      Print logo and elapsed time              (default: +)")
    println("  [+-]printTree                 Output the constructed proof tree        (default: -)")
    println("  -printSMT=filename            Output the problem in SMT-Lib format     (default: \"\")")
    println("  [+-]assert                    Enable runtime assertions                (default: +)")
    println("  -timeout=val                  Set a timeout in milliseconds            (default: infty)")
    println("  -simplifyConstraints=val      How to simplify constraints:")
    println("                                  none:   not at all")
    println("                                  fair:   by fair construction of a proof (default)")
    println("                                  lemmas: by depth-first proof construction using lemmas")
    println("  [+-]traceConstraintSimplifier Show the constraint simplifications done (default: -)")
    println("  [+-]mostGeneralConstraint     Derive the most general constraint for this problem")
    println("                                (quantifier elimination for PA formulae) (default: -)")
    println("  [+-]dnfConstraints            Turn ground constraints into DNF         (default: +)")
    println("  -clausifier=val               Choose the clausifier (none, simple)     (default: none)")
    println("  [+-]posUnitResolution         Resolution of clauses with literals in   (default: +)")
    println("                                the antecedent")
  }
  
  private def printSMT(prover : AbstractFileProver,
                       filename : String,  settings : GlobalSettings) =
    if (Param.PRINT_SMT_FILE(settings) != "") {
      println
      
      def linearise : Unit = {
        import IExpression._
        val completeFormula =
          connect(for (f <- prover.inputFormulas.elements) yield removePartName(f),
                  IBinJunctor.Or)
        SMTLineariser(completeFormula, prover.signature, filename)
      }
      
      if (Param.PRINT_SMT_FILE(settings) != "-") {
        println("Saving in SMT format to " +
                Param.PRINT_SMT_FILE(settings) + " ...")
        val out = new java.io.FileOutputStream(Param.PRINT_SMT_FILE(settings))
        assert(false)
        Console.withOut(out) { linearise }
        out.close
      } else {
        linearise
      }
    }
  
  def proveProblems(settings : GlobalSettings,
                    problems : Seq[(String, java.io.Reader)],
                    userDefStoppingCond : => Boolean) : Unit = {
    if (problems.isEmpty) {
      println("No inputs given, exiting")
      return
    }
    
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    try {
          for ((filename, reader) <- problems) {
            val timeBefore = System.currentTimeMillis
            
            val goalSettings =
              Param.CONSTRAINT_SIMPLIFIER.set(settings.toGoalSettings,
                                              determineSimplifier(settings))
            
            println("Loading " + filename + " ...")
            val prover = new BenchFileProver(reader,
                                             Param.TIMEOUT(settings),
                                             userDefStoppingCond,
                                             settings.toPreprocessingSettings,
                                             goalSettings)
            
            prover.counterModelResult match {
              case BenchFileProver.CounterModel(model) =>  {
                println("Formula is invalid, found a countermodel:")
                println("" + model)
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }              
              case BenchFileProver.NoCounterModel =>  {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
              }
              case BenchFileProver.NoCounterModelCert(cert) =>  {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                println
                println("Certificate: " + cert)
                println("Assumed formulae: " + cert.assumedFormulas)
              }
              case BenchFileProver.NoCounterModelCertInter(cert, inters) => {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                println
                //println("Certificate: " + cert)
                //println("Assumed formulae: " + cert.assumedFormulas)
                println
                println("Interpolants:")
                for (i <- inters) println(i)
              }

              case BenchFileProver.TimeoutCounterModel =>  {

              }
            }
       
            val timeAfter = System.currentTimeMillis
            
            println
            if (Param.LOGO(settings))
              println("" + (timeAfter - timeBefore) + "ms")
              
            printSMT(prover, filename, settings)
            
            /* println
            println(ap.util.Timer)
            ap.util.Timer.reset */
          }
    } catch {
      case e : Throwable => {
        println("ERROR: " + e.getMessage)
        e.printStackTrace
        return
      }
    }
  }

  private def determineSimplifier(settings : GlobalSettings) : ConstraintSimplifier =
    Param.SIMPLIFY_CONSTRAINTS(settings) match {
      case Param.ConstraintSimplifierOptions.None =>
        ConstraintSimplifier.NO_SIMPLIFIER
      case x =>
        ConstraintSimplifier(x == Param.ConstraintSimplifierOptions.Lemmas,
                             Param.DNF_CONSTRAINTS(settings),
                             Param.TRACE_CONSTRAINT_SIMPLIFIER(settings))
    }
  
  def main(args: Array[String]) : Unit = {
    val (settings, inputs) = try { GlobalSettings.fromArguments(args) } catch {
      case e : Throwable => {
        printGreeting
        println
        println(e.getMessage)
        println
        printUsage
        return
      }
    }

    if (Param.LOGO(settings)) {
      printGreeting
      println
    }
    
    proveProblems(settings,
                  for (name <- inputs.projection)
                  yield (name, new java.io.BufferedReader (
                               new java.io.FileReader(new java.io.File (name)))),
                  false)
  }
}
