/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap;

import ap.proof.ConstraintSimplifier
import ap.proof.tree.{ProofTree, QuantifiedTree}
import ap.proof.certificates.{Certificate, DotLineariser,
                              DagCertificateConverter, CertificatePrettyPrinter,
                              CertFormula}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.parameters.{GlobalSettings, Param}
import ap.parser.{SMTLineariser, TPTPLineariser, PrincessLineariser,
                  IFormula, IExpression,
                  IBinJunctor, IInterpolantSpec, INamedPart, IBoolLit, PartName,
                  Internal2InputAbsy, Simplifier, SMTParser2InputAbsy, IFunction,
                  LineariseVisitor}
import ap.util.{Debug, Seqs, Timeout}

object CmdlMain {

  val version = "release 2017-12-06"

  def printGreeting = {
    println("________       _____")                                 
    println("___  __ \\_________(_)________________________________")
    println("__  /_/ /_  ___/_  /__  __ \\  ___/  _ \\_  ___/_  ___/")
    println("_  ____/_  /   _  / _  / / / /__ /  __/(__  )_(__  )")
    println("/_/     /_/    /_/  /_/ /_/\\___/ \\___//____/ /____/")  
    println
    println("A Theorem Prover for First-Order Logic modulo Linear Integer Arithmetic")
    println("(" + version + ")")
    println
    println("(c) Philipp Rümmer, 2009-2017")
    println("(contributions by Angelo Brillout, Peter Backeman, Peter Baumgartner)")
    println("Free software under GNU Lesser General Public License (LGPL).")
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
    println("Standard options:")
    println(" [+-]logo                  Print logo and elapsed time              (default: +)")
    println(" [+-]fullHelp              Print detailed help and exit             (default: -)")
    println(" [+-]version               Print version and exit                   (default: -)")
    println(" [+-]quiet                 Suppress all output to stderr            (default: -)")
    println(" [+-]assert                Enable runtime assertions                (default: -)")
    println(" -inputFormat=val          Specify format of problem file:       (default: auto)")
    println("                             auto, pri, smtlib, tptp")
    println(" [+-]stdin                 Read SMT-LIB 2 problems from stdin       (default: -)")
    println(" [+-]incremental           Incremental SMT-LIB 2 interpreter        (default: -)")
    println("                             (+incremental implies -genTotalityAxioms)")
    println(" -timeout=val              Set a timeout in milliseconds        (default: infty)")
    println(" -timeoutPer=val           Set a timeout per SMT-LIB query (ms) (default: infty)")
    println(" [+-]model                 Compute models or countermodels          (default: -)")
    println(" [+-]unsatCore             Compute unsatisfiable cores              (default: -)")
    println(" [+-]printProof            Output the constructed proof             (default: -)")
    println(" [+-]mostGeneralConstraint Derive the most general constraint for this problem")
    println("                           (quantifier elimination for PA formulae) (default: -)")
    println(" -clausifier=val           Choose the clausifier (none, simple)  (default: none)")
    println(" [+-]genTotalityAxioms     Generate totality axioms for functions   (default: +)")
  }

  def printExoticOptions = {
    println("Exotic options:")
    println(" [+-]printTree             Output the internal constraint tree     (default: -)")
    println(" -printSMT=filename        Output the problem in SMT-LIB format    (default: \"\")")
    println(" -printTPTP=filename       Output the problem in TPTP format       (default: \"\")")
    println(" -printDOT=filename        Output the proof in GraphViz format     (default: \"\")")
    println(" [+-]multiStrategy         Use a portfolio of different strategies  (default: -)")
    println(" -simplifyConstraints=val  How to simplify constraints:")
    println("                             none:   not at all")
    println("                             fair:   fair construction of a proof")
    println("                             lemmas: proof construction with lemmas (default)")
    println(" [+-]traceConstraintSimplifier  Show constraint simplifications     (default: -)")
    println(" [+-]dnfConstraints        Turn ground constraints into DNF         (default: +)")
    println(" [+-]posUnitResolution     Resolution of clauses with literals in   (default: +)")
    println("                             the antecedent")
    println(" -generateTriggers=val     Automatically choose triggers for quant. formulae")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println(" -functionGC=val           Garbage-collect function terms")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println(" [+-]tightFunctionScopes   Keep function application defs. local    (default: +)")
    println(" [+-]boolFunsAsPreds       In smtlib and tptp, encode               (default: -)")
    println("                           boolean functions as predicates")
    println(" -mulProcedure=val         Handling of nonlinear integer formulae")
    println("                             bitShift: shift-and-add axiom")
    println("                             native:   built-in theory solver       (default)")
    println(" -randomSeed=val           Seed for randomisation")
    println("                             <seed>: numeric seed             (default: 1234567)")
    println("                             off:    disable randomisation")
    println(" -adtMeasure=val           Measure to ensure acyclicity of ADTs")
    println("                             relDepth: relative depth of terms")
    println("                             size:     size of terms                (default)")
    println(" -constructProofs=val      Extract proofs")
    println("                             never")
    println("                             ifInterpolating: if \\interpolant occurs (default)")
    println("                             always")
    println(" [+-]elimInterpolantQuants Eliminate quantifiers from interpolants  (default: +)")
//    println(" [+-]simplifyProofs        Simplify extracted proofs                (default: +)")
  }

  //////////////////////////////////////////////////////////////////////////////
  
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
  
  private def printTPTP(prover : AbstractFileProver,
                        filename : String, settings : GlobalSettings) =
    if (Param.PRINT_TPTP_FILE(settings) != "") {
      println
      
      def linearise : Unit = {
        import IExpression._
        TPTPLineariser(prover.originalInputFormula, filename)
      }
      
      if (Param.PRINT_TPTP_FILE(settings) != "-") {
        println("Saving in TPTP format to " +
                Param.PRINT_TPTP_FILE(settings) + " ...")
        val out = new java.io.FileOutputStream(Param.PRINT_TPTP_FILE(settings))
        Console.withOut(out) { linearise }
        out.close
      } else {
        linearise
      }
    }
  
  //////////////////////////////////////////////////////////////////////////////

  private def printCertificate(cert : Certificate,
                               settings : GlobalSettings,
                               prover : Prover)
                              (implicit format : Param.InputFormat.Value) = {
    if (Param.COMPUTE_UNSAT_CORE(settings)) {
      Console.err.println
      Console.err.println("Unsatisfiable core:")
      val usedNames = prover getAssumedFormulaParts cert
      println("{" +
              (((usedNames - PartName.NO_NAME)
                   map (_.toString)).toArray.sorted mkString ", ") +
              "}")
    }

    if (Param.PRINT_CERTIFICATE(settings))
      printTextCertificate(cert, settings, prover)

    if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "")
      printDOTCertificate(cert, settings)
  }

  private def printTextCertificate(cert : Certificate,
                                   settings : GlobalSettings,
                                   prover : Prover)
                                 (implicit format : Param.InputFormat.Value) = {
    println
    doPrintTextCertificate(cert,
                           prover.getFormulaParts,
                           prover.getPredTranslation,
                           format)
  }

  protected[ap] def doPrintTextCertificate(
                      cert : Certificate,
                      rawFormulaParts : Map[PartName, Conjunction],
                      predTranslation : Map[Predicate, IFunction],
                      format : Param.InputFormat.Value) : Unit = {
    val formulaParts = rawFormulaParts mapValues {
      f => CertFormula(f.negate)
    }
    val dagCert = DagCertificateConverter(cert)

    val formulaPrinter = format match {
      case Param.InputFormat.Princess =>
        new CertificatePrettyPrinter.PrincessFormulaPrinter (
          predTranslation
        )
      case Param.InputFormat.TPTP =>
        new CertificatePrettyPrinter.TPTPFormulaPrinter (
          predTranslation
        )
      case Param.InputFormat.SMTLIB =>
        new CertificatePrettyPrinter.SMTLIBFormulaPrinter (
          predTranslation
        )
    }

    val printer = new CertificatePrettyPrinter(formulaPrinter)

    if (format == Param.InputFormat.TPTP)
      println("% SZS output start Proof for theBenchmark")

    printer(dagCert, formulaParts)

    if (format == Param.InputFormat.TPTP)
      println("% SZS output end Proof for theBenchmark")
  }

  private def printDOTCertificate(cert : Certificate,
                                  settings : GlobalSettings) = {
    Console.err.println
     
    if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "-") {
      Console.err.println("Saving certificate in GraphViz format to " +
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
  
  private def printModel(model : IFormula)
                        (implicit format : Param.InputFormat.Value) : Unit =
    format match {
      case Param.InputFormat.SMTLIB =>
        SMTLineariser printModel model
/*      case Param.InputFormat.Princess => {
        val modelStr = PrincessLineariser asString model
        val modelParts = (modelStr split " & ") sortWith {
          (str1, str2) => (!(str1 contains '(') && (str2 contains '(')) ||
                          str1 < str2
        }
        if (modelStr.size > 60)
          println(modelParts.mkString(" &" + System.lineSeparator()))
        else
          println(modelParts.mkString(" & "))
      } */
      case _ =>
        printFormula(model)
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

  def proveProblem(settings : GlobalSettings,
                   name : String,
                   reader : () => java.io.Reader,
                   userDefStoppingCond : => Boolean)
                  (implicit format : Param.InputFormat.Value) : Option[Prover.Result] = {
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    try {
            val timeBefore = System.currentTimeMillis
            val baseSettings = Param.INPUT_FORMAT.set(settings, format)
            
            val prover = if (Param.MULTI_STRATEGY(settings)) {
              import ParallelFileProver._

              def prelPrinter(p : Prover) : Unit = {
                Console.err.println
                printResult(p, baseSettings)
                Console.err.println
              }

              ParallelFileProver(reader,
                                 Param.TIMEOUT(settings),
                                 true,
                                 userDefStoppingCond,
                                 baseSettings,
                                 cascStrategies2016,
                                 1,
                                 3,
                                 Param.COMPUTE_UNSAT_CORE(settings) ||
                                   Param.PRINT_CERTIFICATE(settings) ||
                                   Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "",
                                 prelPrinter _)
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

            printResult(prover, settings)
            
            val timeAfter = System.currentTimeMillis
            
            Console.withOut(Console.err) {
              println
              if (Param.LOGO(settings))
                println("" + (timeAfter - timeBefore) + "ms")
            }
            
            prover match {
              case prover : AbstractFileProver => {
                printSMT(prover, name, settings)
                printTPTP(prover, name, settings)
              }
              case _ => // nothing
            }
            
            /* println
            println(ap.util.Timer)
            ap.util.Timer.reset */
            
            Some(prover.result)
          } catch {
      case _ : StackOverflowError => {
        if (format == Param.InputFormat.SMTLIB)
          println("unknown")
        Console.err.println("Stack overflow, giving up")
        // let's hope that everything is still in a valid state
        None
      }
      case _ : OutOfMemoryError => {
        if (format == Param.InputFormat.SMTLIB)
          println("unknown")
        Console.err.println("Out of memory, giving up")
        System.gc
        // let's hope that everything is still in a valid state
        None
      }
      case e : Throwable => {
        if (format == Param.InputFormat.SMTLIB) {
          println("(error \"" + e.getMessage.replace("\"", "\"\"") + "\")")
	} else {
          println("ERROR: " + e.getMessage)
        }
//         e.printStackTrace
        None
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def proveMultiSMT(settings : GlobalSettings,
                    input : java.io.BufferedReader,
                    userDefStoppingCond : => Boolean) = try {
    val assertions = Param.ASSERTIONS(settings)
    Debug.enableAllAssertions(assertions)
    SimpleAPI.withProver(enableAssert = assertions,
                         sanitiseNames = false,
                         genTotalityAxioms = 
                           Param.GENERATE_TOTALITY_AXIOMS(settings),
                         randomSeed = Param.RANDOM_SEED(settings)) { p =>
      val parser = SMTParser2InputAbsy(settings.toParserSettings, p)
      parser.processIncrementally(input,
                                  Param.TIMEOUT(settings),
                                  Param.TIMEOUT_PER(settings),
                                  userDefStoppingCond)
    }
  } catch {
      case _ : StackOverflowError => {
        println("unknown")
        Console.err.println("Stack overflow, giving up")
      }
      case _ : OutOfMemoryError => {
        println("unknown")
        Console.err.println("Out of memory, giving up")
        System.gc
      }
      case e : Throwable => {
        println("error")
	Console.err.println(e.getMessage)
         e.printStackTrace
      }
  }
  
  def proveProblems(settings : GlobalSettings,
                    name : String,
                    input : () => java.io.BufferedReader,
                    userDefStoppingCond : => Boolean)
                   (implicit format : Param.InputFormat.Value) = {
    Console.err.println("Loading " + name + " ...")
    format match {
      case Param.InputFormat.SMTLIB if (Param.INCREMENTAL(settings)) =>
        proveMultiSMT(settings, input(), userDefStoppingCond)
      case _ => {
        proveProblem(settings, name, input, userDefStoppingCond)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def printResult(prover : Prover,
                  settings : GlobalSettings)
                 (implicit format : Param.InputFormat.Value) = format match {
    case Param.InputFormat.SMTLIB => prover.result match {
              case Prover.Proof(tree, _) => {
                println("unsat")
                if (Param.PRINT_TREE(settings)) Console.withOut(Console.err) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.ProofWithModel(tree, _, model) => {
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
              case Prover.CounterModel(optModel) =>  {
                println("sat")
                for (model <- optModel)
                  printModel(model)
              }
              case Prover.MaybeCounterModel(optModel) =>  {
                println("unknown")
                for (model <- optModel)
                  printModel(model)
              }
              case Prover.NoCounterModel =>  {
                println("unsat")
              }
              case Prover.NoCounterModelCert(cert) =>  {
                println("unsat")
                printCertificate(cert, settings, prover)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                println("unsat")
                printCertificate(cert, settings, prover)
                println("(")
                for (i <- inters) {
                  print("  ")
                  printFormula(i)
                }
                println(")")
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
              case Prover.TimeoutResult() =>  {
                println("unknown")
                Console.err.println("Cancelled or timeout")
              }
    }
      
    case _ => prover.result match {
              case Prover.Proof(tree, constraint) => {
                println("VALID")
                if (!constraint.isTrue ||
                    Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Under the " +
                          (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                             "most-general "
                           else
                             "") + "constraint:")
                  printFormula(constraint)
                }
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.ProofWithModel(tree, constraint, model) => {
                println("VALID")
                if (!constraint.isTrue ||
                    Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Under the " +
                          (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                             "most-general "
                           else
                             "") + "constraint:")
                  printFormula(constraint)
                }
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                model match {
                  case IBoolLit(true) => // nothing
                  case _ if (
                          LineariseVisitor(constraint, IBinJunctor.And) forall {
                            case IExpression.Eq(_, _) => true
                            case _ => false
                          }) => // nothing
                  case _ => {
                    println
                    println("Concrete witness:")
                    printModel(model)
                  }
                }
                if (Param.PRINT_TREE(settings)) {
                  println
                  println("Proof tree:")
                  println(tree)
                }
              }
              case Prover.NoProof(tree) => {
                println("UNKNOWN")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case Prover.Invalid(tree) => {
                println("INVALID")
//                Console.err.println("Number of existential constants: " +
//                                    existentialConstantNum(tree))
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case Prover.CounterModel(optModel) =>  {
                println("INVALID")
                optModel match {
                  case None | Some(IBoolLit(true)) => // nothing
                  case Some(model) => {
                    println
                    println("Countermodel:")
                    printModel(model)
                  }
                }
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case Prover.MaybeCounterModel(optModel) =>  {
                println("UNKNOWN")
                optModel match {
                  case None | Some(IBoolLit(true)) => // nothing
                  case Some(model) => {
                    println
                    println("Possible countermodel:")
                    printModel(model)
                  }
                }
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
              }
              case Prover.NoCounterModel =>  {
                println("VALID")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
              }
              case Prover.NoCounterModelCert(cert) =>  {
                println("VALID")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }

                printCertificate(cert, settings, prover)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                println("VALID")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }

                println
                println("Interpolants:")
                for (i <- inters) printFormula(i)

                printCertificate(cert, settings, prover)
              }
              case Prover.Model(optModel) =>  {
                println("VALID")
                for (model <- optModel) {
                  println
                  println("Under the assignment:")
                  printModel(model)
                }
              }
              case Prover.NoModel =>  {
                println("INVALID")
              }
              case Prover.TimeoutProof(tree) =>  {
                println("CANCELLED/TIMEOUT")
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
              }
              case Prover.TimeoutResult() =>  {
                println("CANCELLED/TIMEOUT")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Current constraint:")
                  println("false")
                }
              }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def main(args: Array[String]) : Unit = doMain(args, false)
  
  def doMain(args: Array[String],
             userDefStoppingCond : => Boolean) : Unit = {
    val (settings, inputs) =
      try {
            GlobalSettings.fromArguments(args, GlobalSettings.DEFAULT)
          } catch {
      case e : Throwable => {
        Console.withOut(Console.err) {
          printGreeting
          println
        }
        println(e.getMessage)
        println
        printUsage
        println
        return
      }
    }

    if (Param.VERSION(settings)) {
      println(version)
      return
    }
          
    if (Param.FULL_HELP(settings)) {
      println(version)
      println
      printUsage
      println
      println
      printExoticOptions
      println
      return
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

    for (filename <- inputs) try {
      implicit val format = determineInputFormat(filename, settings)
      proveProblems(settings,
                    filename,
                    () => new java.io.BufferedReader (
                            new java.io.FileReader(new java.io.File (filename))),
                    userDefStoppingCond)
    } catch {
      case e : Throwable => {
        println("ERROR: " + e.getMessage)
//        e.printStackTrace
      }
    }

    if (Param.STDIN(settings)) {
      Console.err.println("Reading SMT-LIB 2 input from stdin ...")
      proveMultiSMT(settings, Console.in, userDefStoppingCond)
    }
  }

  object NullStream extends java.io.OutputStream {
    def write(b : Int) = {}
  }

}
