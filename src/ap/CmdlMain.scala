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

package ap;

import ap.proof.ConstraintSimplifier
import ap.proof.tree.ProofTree
import ap.parameters.{GlobalSettings, Param}
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
    println("  -generateTriggers=val         Automatically generate triggers for quantified formulae")
    println("                                  none:  not at all")
    println("                                  total: for all total functions         (default)")
    println("                                  all:   for all functions")
    println("  [+-]constructProofs           Extract proofs and interpolants          (default: +)")
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
            
            println("Loading " + filename + " ...")
            val prover = new IntelliFileProver(reader,
                                               Param.TIMEOUT(settings),
                                               Param.MOST_GENERAL_CONSTRAINT(settings),
                                               true,
                                               userDefStoppingCond,
                                               settings)

            println
            
            prover.result match {
              case IntelliFileProver.Proof(tree) => {
                println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                println("" + tree.closingConstraint)
              }
              case IntelliFileProver.ProofWithModel(tree, model) => {
                println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                println("" + tree.closingConstraint)
                if (!model.isTrue) {
                  println
                  println("Concrete witness:")
                  println("" + model)
                }
              }
              case IntelliFileProver.NoProof(_) =>  {
                println("No proof found")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case IntelliFileProver.CounterModel(model) =>  {
                println("Formula is invalid, found a countermodel:")
                println("" + model)
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case IntelliFileProver.NoCounterModel =>  {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
              }
              case IntelliFileProver.NoCounterModelCert(cert) =>  {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                println
                println("Certificate: " + cert)
                println("Assumed formulae: " + cert.assumedFormulas)
                println("Constraint: " + cert.closingConstraint)
              }
              case IntelliFileProver.NoCounterModelCertInter(cert, inters) => {
                println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
//                println
//                println("Certificate: " + cert)
//                println("Assumed formulae: " + cert.assumedFormulas)
//                println("Constraint: " + cert.closingConstraint)
                println
                println("Interpolants:")
                for (i <- inters) println(i)
              }
              case IntelliFileProver.Model(model) =>  {
                println("Formula is valid, satisfying assignment for the existential constants is:")
                println("" + model)
              }
              case IntelliFileProver.NoModel =>  {
                println("No satisfying assignment for the existential constants exists, formula is invalid")
              }
              case IntelliFileProver.TimeoutProof(tree) =>  {
                println("Cancelled or timeout")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  println("" + tree.closingConstraint)
                }
              }
              case IntelliFileProver.TimeoutModel |
                   IntelliFileProver.TimeoutCounterModel =>  {
                println("Cancelled or timeout")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  println("false")
                }
              }
            }
            
            if (Param.PRINT_TREE(settings)) {
              println
              println("Proof tree:")
              println(prover.proofTree)
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

  def main(args: Array[String]) : Unit = {
    val (settings, inputs) =
      try { // switch on proof construction by default in the iPrincess version
            GlobalSettings.fromArguments(args,
                                         Param.PROOF_CONSTRUCTION.set(GlobalSettings.DEFAULT, true))
          } catch {
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
