/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2025 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
                  IFormula, IExpression, IIntLit, IConstant,
                  IBinJunctor, IInterpolantSpec, INamedPart, IBoolLit, PartName,
                  Internal2InputAbsy, Simplifier, SMTParser2InputAbsy, IFunction,
                  LineariseVisitor, TPTPTParser}
import ap.util.{Debug, Seqs, Timeout}

object CmdlMain {

  val version = "2025-11-17"

  /**
   * Flag to enable stack traces being fully printed, for problems
   * specified on the command line.
   */
  var stackTraces = false

  def printGreeting = {
    println("________       _____")                                 
    println("___  __ \\_________(_)________________________________")
    println("__  /_/ /_  ___/_  /__  __ \\  ___/  _ \\_  ___/_  ___/")
    println("_  ____/_  /   _  / _  / / / /__ /  __/(__  )_(__  )")
    println("/_/     /_/    /_/  /_/ /_/\\___/ \\___//____/ /____/")  
    println()
    println("A Theorem Prover for First-Order Logic modulo Linear Integer Arithmetic")
    println("(" + version + ")")
    println()
    println("(c) Philipp Rümmer, 2009-2025")
    println("Contributors: Peter Backeman, Peter Baumgartner, Angelo Brillout, Zafer Esen,")
    println("              Sankalp Gambhir, Amanda Stjerna.")
    println("Free software under BSD-3-Clause.")
    println()
    println("For more information, visit https://philipp.ruemmer.org/princess.shtml")
  }
  
  def printUsage = {
    println("Usage: princess <option>* <inputfile>*")
    println()
    printOptions
  }
  
  def printOptions = {
    println("Standard options:")
    println(" [+-]logo                  Print logo                               (default: +)")
    println(" [+-]runtime               Print elapsed runtime                    (default: +)")
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
    println(" [+-]mostGeneralConstraint Derive a most general constraint         (default: -)")
    println("                           (quantifier elimination for PA formulae) (default: -)")
    println(" -clausifier=val           Choose the clausifier (none, simple)  (default: none)")
    println(" [+-]genTotalityAxioms     Generate totality axioms for functions   (default: +)")
  }

  def printExoticOptions = {
    println("Further general options")
    println("-----------------------")
    println(" -timeoutSec=val           Set a timeout in seconds             (default: infty)")
    println(" [+-]printTree             Output the internal constraint tree     (default: -)")
    println(" -printSMT=filename        Output the problem in SMT-LIB format    (default: \"\")")
    println(" -printTPTP=filename       Output the problem in TPTP format       (default: \"\")")
    println(" -printDOT=filename        Output the proof in GraphViz format     (default: \"\")")
    println(" -portfolio=val            Use a strategy portfolio              (default: none)")
    println("                             none:   off")
    println("                             casc:   Optimised for CASC/TPTP")
    println("                             qf_lia: Optimised for quantifier-free LIA")
    println("                             bv:     Optimised for quantified BV")
    println(" -threads=num              Number of threads to use for portfolio   (default: 1)")
    println(" [+-]threads               Automatically choose number of threads   (default: -)")
    println(" -formulaSign=val          Optionally negate input formula       (default: auto)")
    println("                             positive: do not negate")
    println("                             negative: negate")
    println("                             auto:     choose automatically")
    println(" [+-]equivInlining         Inline simple equivalences p <-> f       (default: +)")
    println(" -inlineSizeLimit=val      Maximum size of functions to inline    (default: 100)")
    println(" -randomSeed=val           Seed for randomisation")
    println("                             <seed>: numeric seed             (default: 1234567)")
    println("                             off:    disable randomisation")
    println(" -logging=flags            Comma-separated list of log flags       (default: \"\")")
    println("                             Flags: tasks, splits, backtracking, stats, lemmas,")
    println("                                    counters, countersCont")
    println()
    println("Proof/interpolation options")
    println("---------------------------")
    println(" -constructProofs=val      Extract proofs")
    println("                             never")
    println("                             ifInterpolating: if \\interpolant occurs (default)")
    println("                             always")
    println(" [+-]elimInterpolantQuants Eliminate quantifiers from interpolants  (default: +)")
//    println(" [+-]simplifyProofs        Simplify extracted proofs                (default: +)")
    println()
    println("Quantifier/constraint options")
    println("-----------------------------")
    println(" [+-]posUnitResolution     Resolution of clauses with literals in   (default: +)")
    println("                           the antecedent")
    println(" [+-]useStrengthenTree     For quantified formulae with inequality  (default: -)")
    println("                           side conditions, use the StrengthenTree")
    println("                           constraint tree constructor")
    println(" -simplifyConstraints=val  How to simplify constraints:")
    println("                             none:   not at all")
    println("                             fair:   fair construction of a proof")
    println("                             lemmas: proof construction with lemmas (default)")
    println(" -mgcFormat=val            Most general constraints in specific format:")
    println("                             any: Unspecified                       (default)")
    println("                             dnf: disjunctive normal form")
    println("                             cnf: conjunctive normal form")
    println(" [+-]traceConstraintSimplifier  Show constraint simplifications     (default: -)")
    println(" [+-]dnfConstraints        Continuously rewrite constraints to DNF  (default: +)")
    println()
    println("Function options")
    println("----------------")
    println(" -generateTriggers=val     Automatically choose triggers for quant. formulae")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println("                             complete, completeFrugal: in combination")
    println("                               with -genTotalityAxioms, in such a way")
    println("                               that completeness is not affected")
    println(" -triggerStrategy=val      How to choose triggers for quantified formulae")
    println("                             allMinimal")
    println("                             allMinimalAndEmpty")
    println("                             allMaximal")
    println("                             maximal                                (default)")
    println("                             maximalOutermost")
    println(" -functionGC=val           Garbage-collect function terms")
    println("                             none:  not at all")
    println("                             total: for all total functions         (default)")
    println("                             all:   for all functions")
    println(" [+-]tightFunctionScopes   Keep function application defs. local    (default: +)")
    println(" [+-]boolFunsAsPreds       In smtlib and tptp, encode               (default: -)")
    println("                           Boolean functions as predicates")
    println(" [+-]reverseFunctionalityPropagation  Infer distinctness of         (default: -)")
    println("                           arguments from distinctness of results")
    println(" [+-]useFunctionalConsistencyTheory  Use dummy theory to represent  (default: -)")
    println("                           functional consistency axioms")
    println()
    println("Theory options")
    println("--------------")
    println(" -mulProcedure=val         Handling of NIA formulae")
    println("                             bitShift: shift-and-add axiom")
    println("                             native:   built-in theory solver       (default)")
    println(" -mulSplitting=val         Splitting in NIA formulae")
    println("                             sign:       +/-/interval splitting     (default)")
    println("                             spherical:  fair value enumeration")
    println(" -mulRandomization=val     Randomization when splitting in NIA formulae")
    println("                             vars:       pick variables randomly")
    println("                             varsCases:  variables + cases randomly (default)")
    println(" -adtMeasure=val           Measure to ensure acyclicity of ADTs")
    println("                             relDepth: relative depth of terms")
    println("                             size:     size of terms                (default)")
    println(" -stringSolver=val         Specify the used string solver")
    println("                             (default: ap.theories.strings.SeqStringTheory)")
    println(" [+-]stringEscapes         Accept extended set of string escapes    (default: -)")
    println(" -seqSolver=val            Specify the used sequence solver")
    println("                             (default: ap.theories.sequences.ArraySeqTheory)")
    println(" -heapSolver=val           Specify the heap theory solver to use")
    println("                             native: native heap theory             (default)")
    println("                             array:  array-backed heap theory")
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private def printSMT(prover : AbstractFileProver,
                       filename : String, settings : GlobalSettings) =
    if (Param.PRINT_SMT_FILE(settings) != "") {
      println()
      
      def linearise : Unit = {
        // TODO: this should be reimplemented, in particular functions be
        // handled properly!
        
        import IExpression._
        prover.interpolantSpecs match {
          case List() =>
            if (prover.signature.existentialConstants.isEmpty &&
                prover.signature.universalConstants.isEmpty) {
              SMTLineariser.printWithDeclsSig(
                              formulas      = List(prover.rawInputFormula),
                              signature     = prover.rawSignature,
                              benchmarkName = filename)
            } else {
              val formulas =
                for (f <- prover.inputFormulas) yield removePartName(f)
              SMTLineariser.printWithDeclsSig(formulas      = formulas,
                                              signature     = prover.signature,
                                              benchmarkName = filename)
            }
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
            val formulas =
              for (part <- left ++ right) yield (common ||| formula(part))
            SMTLineariser.printWithDeclsSig(formulas      = formulas,
                                            signature     = prover.signature,
                                            benchmarkName = filename)
          }
        }
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
      println()
      
      def linearise : Unit = {
        import IExpression._
        TPTPLineariser(prover.rawInputFormula, filename)
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
      Console.err.println()
      Console.err.println("Unsatisfiable core:")
      val usedNames =
        (prover getAssumedFormulaParts cert).filterNot(PartName.predefNamesSet)
      val nameStrings = usedNames map {
        case TPTPTParser.ConjecturePartName(n) => n
        case pn                                => pn.toString
      }

      println("{" +
                (nameStrings.toArray.sorted mkString ", ") +
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
    println()
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
    Console.err.println()
     
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
  
  protected[ap] def determineInputFormat(filename : String,
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
          throw new Exception (
            "could not figure out the input format " +
              "(recognised types: .pri, .smt2, .p)")
      case f => f
  }
  
  private def printFormula(f : IFormula)
                          (implicit format : Param.InputFormat.Value) : Unit =
    format match {
      case Param.InputFormat.SMTLIB => {
        SMTLineariser(f)
        println()
      }
      case _ => {
        PrincessLineariser printExpression f
        println()
      }
    }
  
  private def printModel(model : IFormula)
                        (implicit format : Param.InputFormat.Value) : Unit =
    format match {
      case Param.InputFormat.SMTLIB =>
        SMTLineariser printModel model
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

  private def counterPrintingEnabled(settings : GlobalSettings) : Boolean =
    !Seqs.disjoint(Param.LOG_LEVEL(settings),
                   Set[Param.LOG_FLAG](Param.LOG_COUNTERS,
                                       Param.LOG_COUNTERS_CONT))

  private def needsCounters(settings : GlobalSettings) : Boolean =
    counterPrintingEnabled(settings) ||
    (Param.COUNTER_TIMEOUT(settings) != Long.MaxValue)

  private def warmup(settings : GlobalSettings) : Unit =
    if (Param.WARM_UP(settings)) {
      ap.util.Warmup()
    }

  private def withStatistics[A](settings : GlobalSettings)
                               (comp : => A) : A = {
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    val timeBefore = System.currentTimeMillis

    if (needsCounters(settings))
      ap.util.OpCounters.init
    else
      ap.util.OpCounters.disable

    try {
      comp
    } finally {
      val timeAfter = System.currentTimeMillis
            
      Console.withOut(Console.err) {
        if (Param.PRINT_RUNTIME(settings)) {
          println()
          println("" + (timeAfter - timeBefore) + "ms")
        }
            
        if (Param.LOG_LEVEL(settings) contains Param.LOG_STATS) {
          println()
          println("Statistics:")
          println(ap.util.Timer)
          ap.util.Timer.reset
        }
            
        if (counterPrintingEnabled(settings)) {
          println()
          println("Counters:")
          ap.util.OpCounters.printCounters
        }
      }
    }
  }

  /**
   * Prove or solve problems in the non-incremental mode.
   */
  def proveProblemNonInc(settings : GlobalSettings,
                         name : String,
                         reader : () => java.io.Reader,
                         userDefStoppingCond : => Boolean)
                        (implicit format : Param.InputFormat.Value)
                       : Option[Prover.Result] = {
    try {
      val baseSettings = Param.INPUT_FORMAT.set(settings, format)

      withStatistics(settings) {
        val prover = if (Param.PORTFOLIO(settings) != "none") {
          import ParallelFileProver._

          def prelPrinter(p : Prover) : Unit = {
            Console.err.println()
            printResult(p, baseSettings, name)
            Console.err.println()
          }
              
          val needProof =
            Param.COMPUTE_UNSAT_CORE(settings) ||
            Param.PRINT_CERTIFICATE(settings) ||
            Param.PRINT_DOT_CERTIFICATE_FILE(settings) != ""

          val args =
            ParallelFileProver.ProverArguments(
              reader,
              baseSettings,
              Param.TIMEOUT(settings),
              () => userDefStoppingCond,
              needProof,
              prelPrinter _,
              Param.PORTFOLIO_THREAD_NUM(settings))

          ParallelFileProver(Param.PORTFOLIO(settings), args)

        } else {
          new IntelliFileProver(reader(),
                                AbstractFileProver
                                  .timeoutFromSettings(settings),
                                true,
                                userDefStoppingCond,
                                baseSettings)
        }

        Console.withOut(Console.err) {
          println()
        }

        printResult(prover, settings, name)

        prover match {
          case prover : AbstractFileProver => {
            printSMT(prover, name, settings)
            printTPTP(prover, name, settings)
          }
          case _ => // nothing
        }

        Some(prover.result)
      }
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
        if (stackTraces)
          e.printStackTrace
        if (format == Param.InputFormat.SMTLIB) {
          e.getMessage match {
            case null => println("error")
            case str  => println("(error \"" +
                                   SMTLineariser.escapeString(str) +"\")")
          }
	} else {
          e.getMessage match {
            case null => println("ERROR")
            case str  => println("ERROR: " + str)
          }
        }
        None
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Solve SMT-LIB problems in the incremental mode.
   */
  def proveProblemInc(settings : GlobalSettings,
                      input : java.io.Reader,
                      userDefStoppingCond : => Boolean) = try {
    withStatistics(settings) {
      SimpleAPI.withProver(enableAssert = Param.ASSERTIONS(settings),
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
        if (stackTraces)
          e.printStackTrace
      }
  }

  /**
   * Prove or solve a problem, choosing between incremental and
   * non-incremental mode according to the given settings.
   */
  def proveProblem(settings : GlobalSettings,
                   name : String,
                   input : () => java.io.Reader,
                   userDefStoppingCond : => Boolean)
                  (implicit format : Param.InputFormat.Value) = {
    Console.err.println("Loading " + name + " ...")
    format match {
      case Param.InputFormat.SMTLIB if (Param.INCREMENTAL(settings)) =>
        proveProblemInc(settings, input(), userDefStoppingCond)
      case _ => {
        proveProblemNonInc(settings, name, input, userDefStoppingCond)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def printResult(prover : Prover,
                  settings : GlobalSettings,
                  name : String)
                 (implicit format : Param.InputFormat.Value) = format match {
    case Param.InputFormat.SMTLIB => prover.result match {

      case Prover.Proof(tree, _) => {
        println("unsat")
        maybePrintTree(tree, settings, true)
      }
      case Prover.ProofWithModel(tree, _, model) => {
        println("unsat")
        maybePrintTree(tree, settings, true)
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
      case Prover.Model(_) =>  {
        println("unsat")
      }
      case Prover.AllModels(_, _) =>  {
        println("unsat")
      }
      case Prover.NoModel =>  {
        println("sat")
      }
      case Prover.TimeoutProof(tree) =>  {
        println("unknown")
        Console.err.println("Cancelled or timeout")
        maybePrintTree(tree, settings, true)
      }
      case Prover.TimeoutResult() =>  {
        println("unknown")
        Console.err.println("Cancelled or timeout")
      }

      case result =>
        throw new Exception("Unknown prover result: " + result)
    }

    ////////////////////////////////////////////////////////////////////////////
      
    case Param.InputFormat.TPTP => prover.result match {

      case Prover.Proof(tree, constraint) => {
        printTPTPResult(true, prover, name)
        maybePrintTree(tree, settings, true)
      }

      case Prover.ProofWithModel(tree, constraint, model) => {
        printTPTPResult(true, prover, name)
        maybePrintTree(tree, settings, true)
      }

      case Prover.NoProof(tree) => {
        println("% SZS status GaveUp for " + name)
      }

      case Prover.Invalid(tree) => {
        printTPTPResult(false, prover, name)
      }

      case Prover.CounterModel(optModel) =>  {
        printTPTPResult(false, prover, name)
        maybePrintModel(optModel, "Countermodel", true)
      }

      case Prover.MaybeCounterModel(optModel) =>  {
        println("% SZS status GaveUp for " + name)
        maybePrintModel(optModel, "Possible countermodel", true)
      }

      case Prover.NoCounterModel =>  {
        printTPTPResult(true, prover, name)
      }

      case Prover.NoCounterModelCert(cert) =>  {
        printTPTPResult(true, prover, name)
        printCertificate(cert, settings, prover)
      }

      case Prover.NoCounterModelCertInter(cert, inters) => {
        printTPTPResult(true, prover, name)
        Console.withOut(Console.err) {
          println()
          println("Interpolants:")
          for (i <- inters) printFormula(i)
        }
        printCertificate(cert, settings, prover)
      }

      case Prover.Model(optModel) =>  {
        printTPTPResult(true, prover, name)
        maybePrintModel(optModel, "Under the assignment", true)
      }

      case Prover.AllModels(constraint, optModel) =>  {
        printTPTPResult(true, prover, name)
        maybePrintModel(optModel, "Concrete witness", true)
      }

      case Prover.NoModel =>  {
        printTPTPResult(false, prover, name)
      }

      case Prover.TimeoutProof(tree) =>  {
        println("% SZS status Timeout for " + name)
      }

      case Prover.TimeoutResult() =>  {
        println("% SZS status Timeout for " + name)
      }

      case result =>
        throw new Exception("Unknown prover result: " + result)
    }
      
    ////////////////////////////////////////////////////////////////////////////

    case _ => prover.result match {

      case Prover.Proof(tree, constraint) => {
        println("VALID")
        maybePrintConstraint(constraint, settings)
        maybePrintTree(tree, settings)
      }

      case Prover.ProofWithModel(tree, constraint, model) => {
        println("VALID")
        maybePrintConstraint(constraint, settings)
        model match {
          case _ if (
            LineariseVisitor(constraint, IBinJunctor.And) forall {
              case IExpression.Eq(IConstant(_), IIntLit(_)) => true
              case _ => false
            }) => // nothing
          case _ => {
            println()
            println("Concrete witness:")
            printModel(model)
          }
        }
        maybePrintTree(tree, settings)
      }

      case Prover.NoProof(tree) => {
        println("UNKNOWN")
        maybePrintFixedConstraint(false, "Most-general constraint", settings)
      }

      case Prover.Invalid(tree) => {
        println("INVALID")
        maybePrintFixedConstraint(false, "Most-general constraint", settings)
      }

      case Prover.CounterModel(optModel) =>  {
        println("INVALID")
        maybePrintModel(optModel, "Countermodel")
        maybePrintFixedConstraint(false, "Most-general constraint", settings)
      }

      case Prover.MaybeCounterModel(optModel) =>  {
        println("UNKNOWN")
        maybePrintModel(optModel, "Possible countermodel")
        maybePrintFixedConstraint(false, "Most-general constraint", settings)
      }

      case Prover.NoCounterModel =>  {
        println("VALID")
        maybePrintFixedConstraint(true, "Most-general constraint", settings)
      }

      case Prover.NoCounterModelCert(cert) =>  {
        println("VALID")
        maybePrintFixedConstraint(true, "Most-general constraint", settings)
        printCertificate(cert, settings, prover)
      }

      case Prover.NoCounterModelCertInter(cert, inters) => {
        println("VALID")
        maybePrintFixedConstraint(true, "Most-general constraint", settings)

        println()
        println("Interpolants:")
        for (i <- inters) printFormula(i)

        printCertificate(cert, settings, prover)
      }

      case Prover.Model(optModel) =>  {
        println("VALID")
        maybePrintModel(optModel, "Under the assignment")
      }

      case Prover.AllModels(constraint, optModel) =>  {
        println("VALID")
        if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
          println()
          println("Equivalent constraint:")
          printFormula(constraint)
        }
        maybePrintModel(optModel, "Concrete witness")
      }

      case Prover.NoModel =>  {
        println("INVALID")
        maybePrintFixedConstraint(false, "Equivalent constraint", settings)
      }

      case Prover.TimeoutProof(tree) =>  {
        println("CANCELLED/TIMEOUT")

        if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
          println()
          println("Current constraint:")
          Timeout.withTimeoutMillis(1000) {
            printFormula(tree.closingConstraint)
          }{
            println("(timeout)")
          }
        }

        maybePrintTree(tree, settings)
      }

      case Prover.TimeoutResult() =>  {
        println("CANCELLED/TIMEOUT")
        maybePrintFixedConstraint(false, "Current constraint", settings)
      }

      case result =>
        throw new Exception("Unknown prover result: " + result)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def containsTPTPConjecture(p : Prover) : Boolean =
    p.getInputFormulaParts exists {
      case (p, _) => p.toString endsWith TPTPTParser.CONJECTURE_SUFFIX
    }

  private def printTPTPResult(positive : Boolean,
                              prover   : Prover,
                              name     : String) : Unit = {
    val status = (positive, containsTPTPConjecture(prover)) match {
      case (true,  true ) => "Theorem"
      case (true,  false) => "Unsatisfiable"
      case (false, true ) => "CounterSatisfiable"
      case (false, false) => "Satisfiable"
    }
        
    println("% SZS status " + status + " for " + name)
  }

  private def maybePrintTree(tree     : ProofTree,
                             settings : GlobalSettings,
                             stderr   : Boolean = false) =
    if (Param.PRINT_TREE(settings))
      Console.withOut(if (stderr) Console.err else Console.out) {
        println()
        println("Proof tree:")
        println(tree)
      }
  
  private def maybePrintConstraint(constraint : IFormula,
                                   settings : GlobalSettings)
                                  (implicit format : Param.InputFormat.Value) =
    if (!constraint.isTrue ||
          Param.MOST_GENERAL_CONSTRAINT(settings)) {
      println()
      println("Under the " +
                (if (Param.MOST_GENERAL_CONSTRAINT(settings))
                   "most-general "
                 else
                   "") + "constraint:")
      printFormula(constraint)
    }

  private def maybePrintFixedConstraint(value    : Boolean,
                                        name     : String,
                                        settings : GlobalSettings) =
    if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
      println()
      println(name + ":")
      println(value)
    }

  private def maybePrintModel(optModel : Option[IFormula],
                              name     : String,
                              stderr   : Boolean = false)
                             (implicit format : Param.InputFormat.Value) =
    for (model <- optModel)
      Console.withOut(if (stderr) Console.err else Console.out) {
        println()
        println(name + ":")
        printModel(model)
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
          println()
        }
        println(e.getMessage)
        println()
        printUsage
        println()
        return
      }
    }

    if (Param.VERSION(settings)) {
      println(version)
      return
    }
          
    if (Param.FULL_HELP(settings)) {
      println(version)
      println()
      printUsage
      println()
      println()
      printExoticOptions
      println()
      return
    }
          
    if (Param.QUIET(settings))
      Console setErr NullStream
          
    if (Param.LOGO(settings)) Console.withOut(Console.err) {
      printGreeting
      println()
    }

    if (inputs.isEmpty && !Param.STDIN(settings)) {
      Console.err.println("No inputs given, exiting")
      return
    }

    warmup(settings)

    for (filename <- inputs) try {
      implicit val format = determineInputFormat(filename, settings)
      proveProblem(settings,
                   filename,
                   () => new java.io.BufferedReader (
                           new java.io.FileReader(new java.io.File (filename))),
                   userDefStoppingCond)
    } catch {
      case e : Throwable => {
        println("ERROR: " + e.getMessage)
        if (stackTraces)
          e.printStackTrace
      }
    }

    if (Param.STDIN(settings)) {
      Console.err.println("Reading SMT-LIB 2 input from stdin ...")
      proveProblemInc(settings, Console.in, userDefStoppingCond)
    }
  }

  object NullStream extends java.io.OutputStream {
    def write(b : Int) = {}
  }

}
