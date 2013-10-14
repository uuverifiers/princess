/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.tree.{ProofTree, QuantifiedTree}
import ap.proof.certificates.{Certificate, DotLineariser}
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.parameters.{GlobalSettings, Param}
import ap.parser.{SMTLineariser, PrincessLineariser, IFormula, IExpression,
                  IBinJunctor, IInterpolantSpec, INamedPart, IBoolLit, PartName,
                  Internal2InputAbsy, Simplifier, IncrementalSMTLIBInterface}
import ap.util.{Debug, Seqs, Timeout}

object CmdlMain {

  def printGreeting = {
    println("________       _____")                                 
    println("___  __ \\_________(_)________________________________")
    println("__  /_/ /_  ___/_  /__  __ \\  ___/  _ \\_  ___/_  ___/")
    println("_  ____/_  /   _  / _  / / / /__ /  __/(__  )_(__  )")
    println("/_/     /_/    /_/  /_/ /_/\\___/ \\___//____/ /____/")  
    println
    println("A Theorem Prover for First-Order Logic modulo Linear Integer Arithmetic")
    println("(CASC version 2013-09-19)")
    println
    println("(c) Philipp Rümmer, 2009-2013")
    println("(contributions by Angelo Brillout, Peter Baumgartner, Aleksandar Zeljic)")
    println("Free software under GNU General Public License (GPL).")
    println("Bug reports to ph_r@gmx.net")
    println
    println("For more information, visit http://www.philipp.ruemmer.org/princess.shtml")
  }
  
  def printUsage = {
    println("Usage: princess <option>* <inputfile>*")
    println
    printOptions
  }
  
  def printOptions = {
    println("Options:")
    println(" [+-]logo                  Print logo and elapsed time              (default: +)")
    println(" [+-]quiet                 Suppress all output to stderr            (default: -)")
    println(" [+-]printTree             Output the constructed proof tree        (default: -)")
    println(" -inputFormat=val          Specify format of problem file:       (default: auto)")
    println("                             auto, pri, smtlib, tptp")
    println(" [+-]stdin                 Read SMT-LIB 2 problems from stdin       (default: -)")
    println(" -printSMT=filename        Output the problem in SMT-Lib format    (default: \"\")")
    println(" -printDOT=filename        Output the proof in GraphViz format     (default: \"\")")
    println(" [+-]assert                Enable runtime assertions                (default: -)")
    println(" -timeout=val              Set a timeout in milliseconds        (default: infty)")
    println(" [+-]multiStrategy         Use a portfolio of different strategies  (default: -)")
    println(" -simplifyConstraints=val  How to simplify constraints:")
    println("                             none:   not at all")
    println("                             fair:   fair construction of a proof (default)")
    println("                             lemmas: depth-first proof construction using lemmas")
    println(" [+-]traceConstraintSimplifier  Show constraint simplifications     (default: -)")
    println(" [+-]mostGeneralConstraint Derive the most general constraint for this problem")
    println("                           (quantifier elimination for PA formulae) (default: -)")
    println(" [+-]dnfConstraints        Turn ground constraints into DNF         (default: +)")
    println(" -clausifier=val           Choose the clausifier (none, simple)  (default: none)")
    println(" [+-]posUnitResolution     Resolution of clauses with literals in   (default: +)")
    println("                           the antecedent")
    println(" -generateTriggers=val     Automatically choose triggers for quant. formulae")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println(" -functionGC=val           Garbage-collect function terms")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println(" [+-]tightFunctionScopes   Keep function application defs. local    (default: +)")
    println(" [+-]genTotalityAxioms     Generate totality axioms for functions   (default: +)")
    println(" [+-]boolFunsAsPreds       In smtlib and tptp, encode               (default: -)")
    println("                           boolean functions as predicates")
    println(" -constructProofs=val      Extract proofs")
    println("                             never")
    println("                             ifInterpolating: if \\interpolant occurs (default)")
    println("                             always")
    println(" [+-]simplifyProofs        Simplify extracted proofs                (default: +)")
    println(" [+-]elimInterpolantQuants Eliminate quantifiers from interpolants  (default: +)")
  }
  
  private def printSMT(prover : AbstractFileProver,
                       filename : String, settings : GlobalSettings) =
    if (Param.PRINT_SMT_FILE(settings) != "") {
      println
      
      def linearise : Unit = {
        import IExpression._
        val formulas = prover.interpolantSpecs match {
          case List() =>
            for (f <- prover.inputFormulas) yield removePartName(f)
          case IInterpolantSpec(left, right) :: _ => {
            def formula(name : PartName) =
              removePartName(prover.inputFormulas.find({
                               case INamedPart(`name`, _) => true
                               case _ => false
                             }).getOrElse(false))
              
            val common = formula(PartName.NO_NAME)
            
            // extract the order of formula parts from the first
            // interpolant specification; this does not quite do the right
            // thing for the axioms of uninterpreted functions, but should
            // work otherwise
            for (part <- left ++ right) yield (common ||| formula(part))
          }
        }

        SMTLineariser(formulas, prover.signature, filename)
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
  
  private def printDOTCertificate(cert : Certificate, settings : GlobalSettings) =
    if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "") {
      println
      
      if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "-") {
        println("Saving certificate in GraphViz format to " +
                Param.PRINT_DOT_CERTIFICATE_FILE(settings) + " ...")
        val out =
          new java.io.FileOutputStream(Param.PRINT_DOT_CERTIFICATE_FILE(settings))
        Console.withOut(out) { DotLineariser(cert) }
        out.close
      } else {
        DotLineariser(cert)
      }
    }
  
  private def determineInputFormat(filename : String,
                                   settings : GlobalSettings)
                                  : Param.InputFormat.Value =
    Param.INPUT_FORMAT(settings) match {
      case Param.InputFormat.Auto =>
        // try to guess the file type from the extension
        if (filename endsWith ".pri")
          Param.InputFormat.Princess
        else if (filename endsWith ".smt2")
          Param.InputFormat.SMTLIB
        else if (filename endsWith ".p")
          Param.InputFormat.TPTP
        else
          throw new Exception ("could not figure out the input format (recognised types: .pri, .smt2, .p)")
      case f => f
  }
  
  private def printFormula(f : IFormula)
                          (implicit format : Param.InputFormat.Value) : Unit =
    format match {
      case Param.InputFormat.SMTLIB => {
        SMTLineariser(f)
        println
      }
      case _ => {
        PrincessLineariser printExpression f
        println
      }
    }
  
  private def printFormula(c : Conjunction)
                          (implicit format : Param.InputFormat.Value) : Unit =
    printFormula((new Simplifier)(Internal2InputAbsy(c)))
  
  private def existentialConstantNum(p : ProofTree) : Int = p match {
    case QuantifiedTree(Quantifier.EX, consts, subtree) =>
      existentialConstantNum(subtree) + consts.size
    case t =>
      (for (st <- t.subtrees.iterator) yield existentialConstantNum(st)).sum
  }

  private var lastFilename : String = ""
  var positiveResult : String = "Theorem"
  var negativeResult : String = "CounterSatisfiable"
    
  var domain_size : ConstantTerm = new ConstantTerm("domain_size")

  var conjectureNum : Int = -1

  //////////////////////////////////////////////////////////////////////////////
  
  def toSetting(str : String, baseSettings : GlobalSettings) = {
    var s = baseSettings
    s = Param.TRIGGERS_IN_CONJECTURE.set(s, str(0) == '1')
    s = Param.GENERATE_TOTALITY_AXIOMS.set(s, str(1) == '1')
    s = Param.TIGHT_FUNCTION_SCOPES.set(s, str(2) == '1')
    s = Param.CLAUSIFIER.set(s,
        if (str(3) == '0')
          Param.ClausifierOptions.Simple
        else
          Param.ClausifierOptions.None)
    s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, str(4) == '1')
    s = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(s, str(5) == '1')
    s = Param.TRIGGER_STRATEGY.set(s, str(6) match {
      case '0' => Param.TriggerStrategyOptions.AllMaximal
      case '1' => Param.TriggerStrategyOptions.Maximal
      case '2' => Param.TriggerStrategyOptions.AllMinimal
    })
    s
  }
              
  def toOptionList(strategy : String) : String = {
    var s = ""
    s = s + " " + (if (strategy.charAt(0)=='0') "-" else "+") + "triggersInConjecture"
    s = s + " " + (if (strategy.charAt(1)=='0') "-" else "+") + "genTotalityAxioms"
    s = s + " " + (if (strategy.charAt(2)=='0') "-" else "+") + "tightFunctionScopes"
    s = s + " -clausifier=" + (if (strategy.charAt(3)=='0') "simple" else "none")
    s = s + " " + (if (strategy.charAt(4)=='0') "-" else "+") + "reverseFunctionalityPropagation"
    s = s + " " + (if (strategy.charAt(5)=='0') "-" else "+") + "boolFunsAsPreds"
    
    s = s + " -triggerStrategy=" + (
       if(strategy.charAt(6)=='0')
         "allMaximal"
       else if(strategy.charAt(6)=='1')
         "maximal"
       else
         "allMinimal"
    )
    
    s
  }

  //////////////////////////////////////////////////////////////////////////////

  def proveProblem(settings : GlobalSettings,
                   name : String,
                   reader : () => java.io.Reader,
                   userDefStoppingCond : => Boolean)
                  (implicit format : Param.InputFormat.Value) : Option[Prover.Result] = {
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    try {
            val timeBefore = System.currentTimeMillis

            lastFilename = (name split "/").last stripSuffix ".p"
            conjectureNum = -1
            
            var rawStrategies =
              List(("1010002", 15000),
                   ("1110110", 15000),
                   ("0010101", 13000),
                   ("0000000", 20000),
                   ("0011001", 20000),
                   ("0111100", 5000),
                   ("0010012", 50000),
                   ("1101000", Int.MaxValue),
                   ("1001102", 10000),
                   ("0011011", Int.MaxValue),
                   ("1001001", 10000),
                   ("1011002", Int.MaxValue))
                
            var conjNum = 0
            var result : Prover.Result = null

            while (result == null) {
              val baseSettings =
                Param.INPUT_FORMAT.set(
                Param.CONJECTURE_TO_PROVE.set(settings, Some(conjNum)), format)
              
              val prover = if (Param.MULTI_STRATEGY(settings)) {
                import ParallelFileProver._
                
                val strategies = for ((str, to) <- rawStrategies) yield {
                  val s = Param.CLAUSIFIER_TIMEOUT.set(toSetting(str, baseSettings),
                                                       to min 50000)
                  val options = toOptionList(str)
                  Configuration(s, Param.GENERATE_TOTALITY_AXIOMS(s), options, to)
                }
                
                new ParallelFileProver(reader,
                                       Param.TIMEOUT(settings),
                                       true,
                                       userDefStoppingCond,
                                       strategies,
                                       3)
  
              } else {
                new IntelliFileProver(reader(),
                                      Param.TIMEOUT(settings),
                                      true,
                                      userDefStoppingCond,
                                      baseSettings)
              }
  
              Console.withOut(Console.err) {
                println
              }
  
              prover.result match {
                case _ : Prover.Proof |
                     _ : Prover.ProofWithModel |
                     Prover.NoCounterModel |
                     _ : Prover.NoCounterModelCert |
                     _ : Prover.NoCounterModelCertInter |
                     _ : Prover.Model if (conjNum < conjectureNum - 1) => {
                  conjNum = conjNum + 1
                  Console.err.println("" + (conjectureNum - conjNum) + " conjectures left")

                  prover match {
                    case prover : ParallelFileProver =>
                      // reorder strategies, to start with the one that
                      // worked last time
                      rawStrategies =
                        rawStrategies(prover.successfulProver) ::
                        (rawStrategies take prover.successfulProver) :::
                        (rawStrategies drop (prover.successfulProver + 1))
                    case _ => // nothing
                  }
                }
                case _ =>
                  result = prover.result
              }
            }

            printResult(result, settings)
            
            val timeAfter = System.currentTimeMillis
            
            Console.withOut(Console.err) {
              println
              if (Param.LOGO(settings))
                println("" + (timeAfter - timeBefore) + "ms")
            }
            
            /* println
            println(ap.util.Timer)
            ap.util.Timer.reset */
            
            Some(result)
          } catch {
      case _ : StackOverflowError => Console.withOut(Console.err) {
        if (format == Param.InputFormat.SMTLIB)
          println("unknown")
        println("Stack overflow, giving up")
        // let's hope that everything is still in a valid state
        None
      }
      case _ : OutOfMemoryError => Console.withOut(Console.err) {
        if (format == Param.InputFormat.SMTLIB)
          println("unknown")
        println("Out of memory, giving up")
        System.gc
        // let's hope that everything is still in a valid state
        None
      }
      case e : Throwable => {
        format match {
          case Param.InputFormat.SMTLIB =>
            println("error")
          case Param.InputFormat.TPTP =>
            println("% SZS status Error for " + lastFilename)
        }
        Console.err.println("ERROR: " + e.getMessage)
//         e.printStackTrace
        None
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def proveMultiSMT(settings : GlobalSettings,
                    input : java.io.BufferedReader,
                    userDefStoppingCond : => Boolean) = {
    implicit val format = Param.InputFormat.SMTLIB
    val interface = new IncrementalSMTLIBInterface {
      protected def solve(input : String) : Option[Prover.Result] = {
        Console.err.println("Checking satisfiability ...")
        proveProblem(settings,
                     "SMT-LIB 2 input",
                     () => new java.io.StringReader(input),
                     userDefStoppingCond)
      }
    }
    interface.readInputs(input, settings)
  }
  
  def proveProblems(settings : GlobalSettings,
                    name : String,
                    input : () => java.io.BufferedReader,
                    userDefStoppingCond : => Boolean)
                   (implicit format : Param.InputFormat.Value) = {
    Console.err.println("Loading " + name + " ...")
    format match {
      case Param.InputFormat.SMTLIB =>
        proveMultiSMT(settings, input(), userDefStoppingCond)
      case _ => {
        proveProblem(settings, name, input, userDefStoppingCond)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def printResult(res : Prover.Result,
                  settings : GlobalSettings)
                 (implicit format : Param.InputFormat.Value) = format match {
    case Param.InputFormat.SMTLIB => res match {
              case Prover.Proof(tree) => {
                println("unsat")
                if (Param.PRINT_TREE(settings)) Console.withOut(Console.err) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.ProofWithModel(tree, model) => {
                println("unsat")
                if (Param.PRINT_TREE(settings)) Console.withOut(Console.err) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.NoProof(_) =>  {
                println("unknown")
              }
              case Prover.Invalid(_) =>  {
                println("sat")
              }
              case Prover.CounterModel(model) =>  {
                println("sat")
                Console.withOut(Console.err) {
                  println
                  println("Model:")
                  printFormula(model)
                }
              }
              case Prover.NoCounterModel =>  {
                println("unsat")
              }
              case Prover.NoCounterModelCert(cert) =>  {
                println("unsat")
                printDOTCertificate(cert, settings)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                println("unsat")
                printDOTCertificate(cert, settings)
              }
              case Prover.Model(model) =>  {
                println("unsat")
              }
              case Prover.NoModel =>  {
                println("sat")
              }
              case Prover.TimeoutProof(tree) =>  {
                println("unknown")
                Console.err.println("Cancelled or timeout")
                if (Param.PRINT_TREE(settings)) Console.withOut(Console.err) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.TimeoutModel | Prover.TimeoutCounterModel =>  {
                println("unknown")
                Console.err.println("Cancelled or timeout")
              }
    }

    case Param.InputFormat.TPTP => res match {
              case Prover.Proof(tree) => {
                Console.err.println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                Console.withOut(Console.err) {
                  printFormula(tree.closingConstraint)
                }
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.ProofWithModel(tree, model) => {
                Console.err.println("Formula is valid, resulting " +
                        (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                           "most-general "
                         else
                           "") + "constraint:")
                Console.withOut(Console.err) {
                  printFormula(tree.closingConstraint)
                }
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                model match {
                  case IBoolLit(true) => // nothing
                  case _ if ({
                               val c = tree.closingConstraint
                               c.arithConj.positiveEqs.size == c.size
                              }) => // nothing
                  case _ => {
                    println
                    println("Concrete witness:")
                    printFormula(model)
                  }
                }
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoProof(tree) =>  {
                Console.err.println("No proof found")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                
                println("% SZS status GaveUp for " + lastFilename)
              }
              case Prover.Invalid(tree) => {
                Console.err.println("No proof found")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                println("% SZS status " + negativeResult + " for " + lastFilename)
              }
              case Prover.CounterModel(model) =>  {
                Console.withOut(Console.err) {
                  println("Formula is invalid, found a countermodel:")
                  printFormula(model)
                }
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                
                println("% SZS status " + negativeResult + " for " + lastFilename)
              }
              case Prover.NoCounterModel =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoCounterModelCert(cert) =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                Console.withOut(Console.err) {
                  println
                  println("Certificate: " + cert)
                  println("Assumed formulae: " + cert.assumedFormulas)
                  print("Constraint: ")
                  printFormula(cert.closingConstraint)
                }
                
                printDOTCertificate(cert, settings)

                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
//                println
//                println("Certificate: " + cert)
//                println("Assumed formulae: " + cert.assumedFormulas)
//                println("Constraint: " + cert.closingConstraint)
                Console.withOut(Console.err) {
                  println
                  println("Interpolants:")
                  for (i <- inters) printFormula(i)
                }

                printDOTCertificate(cert, settings)
                
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.Model(model) =>  {
                Console.withOut(Console.err) {
                  println("Formula is valid, satisfying assignment for the existential constants is:")
                  printFormula(model)
                }
                println("% SZS status " + positiveResult + " for " + lastFilename)
              }
              case Prover.NoModel =>  {
                Console.err.println("No satisfying assignment for the existential constants exists, formula is invalid")
                println("% SZS status " + negativeResult + " for " + lastFilename)
              }
              case Prover.TimeoutProof(tree) =>  {
                Console.err.println("Cancelled or timeout")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  Timeout.withTimeoutMillis(1000) {
                    printFormula(tree.closingConstraint)
                  }{
                    println("(timeout)")
                  }
                }
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
                println("% SZS status Timeout for " + lastFilename)
              }
              case Prover.TimeoutModel | Prover.TimeoutCounterModel =>  {
                Console.err.println("Cancelled or timeout")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  println("false")
                }
                println("% SZS status Timeout for " + lastFilename)
              }
            }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def main(args: Array[String]) : Unit = {
    val (settings, inputs) =
      try { // switch on proof construction by default in the iPrincess version
            GlobalSettings.fromArguments(args, GlobalSettings.DEFAULT)
          } catch {
      case e : Throwable => {
        Console.withOut(Console.err) {
          printGreeting
          println
          println(e.getMessage)
          println
          printUsage
        }
        return
      }
    }

    if (Param.QUIET(settings))
      Console setErr NullStream
          
    if (Param.LOGO(settings)) Console.withOut(Console.err) {
      printGreeting
      println
    }

    if (inputs.isEmpty && !Param.STDIN(settings)) {
      Console.err.println("No inputs given, exiting")
      return
    }

    for (filename <- inputs) {
      implicit val format = determineInputFormat(filename, settings)
      proveProblems(settings,
                    filename,
                    () => new java.io.BufferedReader (
                            new java.io.FileReader(new java.io.File (filename))),
                    false)
    }

    if (Param.STDIN(settings)) {
      Console.err.println("Reading SMT-LIB 2 input from stdin ...")
      proveMultiSMT(settings, Console.in, false)
    }
  }
  
  object NullStream extends java.io.OutputStream {
    def write(b : Int) = {}
  }

}
