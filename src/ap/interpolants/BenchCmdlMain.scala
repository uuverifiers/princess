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
import ap.util.{Debug, Seqs, CmdlParser}

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
            
            println("Loading " + filename + " ...")
            val prover = new BenchFileProver(filename,
                                             reader,
                                             mode, num,
                                             Param.TIMEOUT(settings),
                                             userDefStoppingCond,
                                             settings)
            
            val timeAfter = System.currentTimeMillis
            
            println
            if (Param.LOGO(settings))
              println("" + (timeAfter - timeBefore) + "ms")
              
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

  private var mode = BenchFileProver.Mode.ProofBased
  private var num = 0
    
  def main(args: Array[String]) : Unit = {
    var remainingArgs = new scala.collection.mutable.ArrayBuffer[String]
    for (a <- args)
      a match {
        case CmdlParser.ValueOpt("startNum", CmdlParser.IntVal(n)) =>
          num = n
        case CmdlParser.ValueOpt("mode", "proofbased") =>
          mode = BenchFileProver.Mode.ProofBased
        case CmdlParser.ValueOpt("mode", "qebased") =>
          mode = BenchFileProver.Mode.QEBased
        case CmdlParser.ValueOpt("mode", "smtdump") =>
          mode = BenchFileProver.Mode.SMTDump
        case _ =>
          remainingArgs += a
      }
    
    val (settings, inputs) = try { GlobalSettings.fromArguments(remainingArgs) } catch {
      case e : Throwable => {
        printGreeting
        println
        println(e.getMessage)
        println
        printUsage
        return
      }
    }

    proveProblems(settings,
                  for (name <- inputs.projection)
                  yield (name, new java.io.BufferedReader (
                               new java.io.FileReader(new java.io.File (name)))),
                  false)
  }
}
