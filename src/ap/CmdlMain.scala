/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.parameters.{GlobalSettings, Param}
import ap.parser.{SMTLineariser, TPTPLineariser, PrincessLineariser,
                  IFormula, IExpression,
                  IBinJunctor, IInterpolantSpec, INamedPart, IBoolLit, PartName,
                  Internal2InputAbsy, Simplifier, IncrementalSMTLIBInterface,
                  SMTParser2InputAbsy}
import ap.util.{Debug, Seqs, Timeout}

object CmdlMain {

  class GaveUpException(_msg : String) extends Exception(_msg)
  val version = "CASC build 2016-02-18"

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
    println("(c) Philipp Rümmer, 2009-2016")
    println("(contributions by Peter Backeman, Peter Baumgartner,")
    println("                  Angelo Brillout, Aleksandar Zeljic)")
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
    println(" -clausifier=val           Choose the clausifier (none, simple)  (default: none)")
    println(" [+-]mostGeneralConstraint Derive the most general constraint for this problem")
    println("                           (quantifier elimination for PA formulae) (default: -)")
    println(" [+-]genTotalityAxioms     Generate totality axioms for functions   (default: +)")
    println(" [+-]unsatCore             Compute unsatisfiable cores              (default: -)")
    println(" [+-]printProof            Output the constructed proof             (default: -)")
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
    println("                             total: for all total functions")
    println("                             all:   for all functions               (default)")
    println(" -functionGC=val           Garbage-collect function terms")
    println("                             none:  not at all")
    println("                             total: for all total functions")
    println("                             all:   for all functions               (default)")
    println(" [+-]tightFunctionScopes   Keep function application defs. local    (default: +)")
    println(" -genTotalityAxioms=val    Generation of totality axioms for functions")
    println("                             none:  no totality axioms at all")
    println("                             ctors: axioms only for constructors")
    println("                             all:   axioms for all functions        (default)")
    println(" [+-]boolFunsAsPreds       In smtlib and tptp, encode               (default: -)")
    println("                           boolean functions as predicates")
    println(" [+-]triggersInConjecture  Generate triggers in conjectures         (default: +)")
    println(" [+-]splitConjectures      Split conjunctions in conjectures        (default: -)")
    println(" -mulProcedure=val         Handling of nonlinear integer formulae")
    println("                             bitShift: shift-and-add axiom")
    println("                             native:   built-in theory solver       (default)")
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
                               prover : Prover,
                               lastFilename : String)
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
      printTextCertificate(cert, settings, prover, lastFilename)

    if (Param.PRINT_DOT_CERTIFICATE_FILE(settings) != "")
      printDOTCertificate(cert, settings)
  }

  private def printTextCertificate(cert : Certificate,
                                   settings : GlobalSettings,
                                   prover : Prover,
                                   lastFilename : String)
                                 (implicit format : Param.InputFormat.Value) = {
    Console.err.println

    val dagCert = DagCertificateConverter(cert)
    val formulaParts = prover.getFormulaParts mapValues {
      f => CertFormula(f.negate)
    }

    val formulaPrinter = format match {
      case Param.InputFormat.Princess =>
        new CertificatePrettyPrinter.PrincessFormulaPrinter (
          prover.getPredTranslation
        )
      case Param.InputFormat.TPTP =>
        new CertificatePrettyPrinter.TPTPFormulaPrinter (
          prover.getPredTranslation
        )
      case Param.InputFormat.SMTLIB =>
        new CertificatePrettyPrinter.SMTLIBFormulaPrinter (
          prover.getPredTranslation
        )
    }

    val printer = new CertificatePrettyPrinter(formulaPrinter)

    if (format == Param.InputFormat.TPTP)
      println("% SZS output start Proof for " + lastFilename)

    printer(dagCert, formulaParts)

    if (format == Param.InputFormat.TPTP)
      println("% SZS output end Proof for " + lastFilename)
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
  
  private def printFormula(c : Conjunction)
                          (implicit format : Param.InputFormat.Value) : Unit =
    printFormula((new Simplifier)(Internal2InputAbsy(c)))
  
  private def existentialConstantNum(p : ProofTree) : Int = p match {
    case QuantifiedTree(Quantifier.EX, consts, subtree) =>
      existentialConstantNum(subtree) + consts.size
    case t =>
      (for (st <- t.subtrees.iterator) yield existentialConstantNum(st)).sum
  }

  //////////////////////////////////////////////////////////////////////////////
  
  def toSetting(str : String, baseSettings : GlobalSettings) = {
    var s = baseSettings
    s = Param.TRIGGERS_IN_CONJECTURE.set(s, str(0) == '1')
    s = Param.GENERATE_TOTALITY_AXIOMS.set(s, str(1) match {
          case '0' => Param.TotalityAxiomOptions.None
          case '1' => Param.TotalityAxiomOptions.Ctors
          case '2' => Param.TotalityAxiomOptions.All
        })
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
      case '3' => Param.TriggerStrategyOptions.AllMinimalAndEmpty
      case '4' => Param.TriggerStrategyOptions.AllUni
      case '5' => Param.TriggerStrategyOptions.MaximalOutermost
    })
    s = Param.REAL_RAT_SATURATION_ROUNDS.set(s, (str(7) - '0').toInt)
    s = Param.IGNORE_QUANTIFIERS.set(s, str(8) == '1' || str(8) == '2')
    s = Param.PROOF_CONSTRUCTION_GLOBAL.set(s,
          if (str(8) == '2')
            Param.ProofConstructionOptions.Always
          else
            Param.ProofConstructionOptions.Never)
    s = Param.TRIGGER_GENERATION.set(s, str(9) match {
      case '0' => Param.TriggerGenerationOptions.All
      case '1' => Param.TriggerGenerationOptions.Complete
      case '2' => Param.TriggerGenerationOptions.CompleteFrugal
    })
    s
  }

  def toOptionList(strategy : String) : String = {
    var s = ""
    s = s + " " + (if (strategy.charAt(0)=='0') "-" else "+") + "triggersInConjecture"
    s = s + " -genTotalityAxioms=" + (strategy.charAt(1) match {
                                        case '0' => "none"
                                        case '1' => "ctors"
                                        case '2' => "all"
                                      })
    s = s + " " + (if (strategy.charAt(2)=='0') "-" else "+") + "tightFunctionScopes"
    s = s + " -clausifier=" + (if (strategy.charAt(3)=='0') "simple" else "none")
    s = s + " " + (if (strategy.charAt(4)=='0') "-" else "+") + "reverseFunctionalityPropagation"
    s = s + " " + (if (strategy.charAt(5)=='0') "-" else "+") + "boolFunsAsPreds"
    
    s = s + " -triggerStrategy=" + (
       if(strategy.charAt(6)=='0')
         "allMaximal"
       else if(strategy.charAt(6)=='1')
         "maximal"
       else if(strategy.charAt(6)=='2')
         "allMinimal"
       else if(strategy.charAt(6)=='3')
         "allMinimalAndEmpty"
       else if(strategy.charAt(6)=='4')
         "allUni"
       else
         "maximalOutermost"
    )

    s = s + " -realRatSaturationRounds=" + strategy.charAt(7)
    s = s + " " + (if (strategy.charAt(8)=='0') "-" else "+") + "ignoreQuantifiers"
    s = s + " -proofConstruction=" +
              (if (strategy.charAt(8)=='2') "always" else "never")
    s = s + " -generateTriggers=" + (
      if (strategy.charAt(9)=='0')
        "all"
      else if (strategy.charAt(9)=='1')
        "complete"
      else
        "completeFrugal"
    )
    
    s
  }

  //////////////////////////////////////////////////////////////////////////////

  val domain_size : ConstantTerm = new ConstantTerm("domain_size")

  def proveProblem(settings : GlobalSettings,
                   name : String,
                   reader : () => java.io.Reader,
                   userDefStoppingCond : => Boolean)
                  (implicit format : Param.InputFormat.Value) : Option[Prover.Result] = {
    Debug.enableAllAssertions(Param.ASSERTIONS(settings))

    var lastFilename : String = ""
    val fileProperties = new Param.FileProperties

    val settings2 = Param.INPUT_FORMAT.set(
                    Param.FILE_PROPERTIES.set(settings,
                                           fileProperties), format)

    try {
            val timeBefore = System.currentTimeMillis

            lastFilename = (name split "/").last stripSuffix ".p"
            fileProperties.conjectureNum = -1
            
            var rawStrategies =
List(
("1000011020",6000,4000),
("1010000020",2000,800),
("0011105000",11000,600),
("1010114020",4000,200),
("1111113000",4000,600),
("1101001020",16000,16000),
("1001004020",9000,2600),
("1101014000",8000,200),
("0011002010",48000,48000),
("0001001010",43000,40000),
("1000011021",1000,1000),
("1011111001",1000,1000),
("0100004000",2000,800),
("1000105001",24000,24000),
("0001101010",47000,200),
("0011111022",4000,4000),
("1001011020",56000,200),
("1001100012",3000,3000),
("0011005020",32000,32000),
("1001001021",3000,400))
/*
List(
("1001001020",13000,4000),
("1010004000",60000,800),
("1011110101",2000,1600),
("0100102100",55000,200),
("0000105000",1000,1000),
("1000112020",1000,400),
("1001000120",3000,2800),
("1200113000",1000,1000),
("0011105100",6000,6000),
("1001111101",9000,2200),
("1101003000",37000,200),
("1101011000",53000,53000),
("1001105101",36000,23000),
("1010004100",12000,400),
("1201003100",24000,10000),
("1010015010",59000,3000),
("1001000010",60000,26000),
("0000005101",7000,3000),
("0000105100",31000,11000),
("1001005000",1000000,16000)
)
*/
        
            var conjNum = 0
	    var prover : Prover = null
            var result : Prover.Result = null
            var prelResultPrinted : Prover.Result = null

            while (result == null) {
              val baseSettings =
                Param.CLAUSIFIER_TIMEOUT.set(
                Param.CONJECTURE_TO_PROVE.set(settings2,
                             if (Param.SPLIT_CONJECTURES(settings2))
                               Some(conjNum)
                             else
                               None), 15000)
              
              prover = if (Param.MULTI_STRATEGY(settings)) {
                import ParallelFileProver._
                
                val strategies = for ((str, to, seq) <- rawStrategies) yield {
                  val s = Param.CLAUSIFIER_TIMEOUT.set(toSetting(str, baseSettings),
                                                       to min 50000)
                  Configuration(s, toOptionList(str), to, seq)
                }
                
                def prelPrinter(p : Prover) : Unit = {
                  prelResultPrinted = p.result
                  Console.err.println
                  printResult(prelResultPrinted, p, settings2, lastFilename)
                  Console.err.println
                }

                new ParallelFileProver(reader,
                                       Param.TIMEOUT(settings),
                                       true,
                                       userDefStoppingCond,
                                       strategies,
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
  
              prover.result match {
                case _ : Prover.Proof |
                     _ : Prover.ProofWithModel |
                     Prover.NoCounterModel |
                     _ : Prover.NoCounterModelCert |
                     _ : Prover.NoCounterModelCertInter |
                     _ : Prover.Model if (conjNum < fileProperties.conjectureNum - 1) => {
                  conjNum = conjNum + 1
                  Console.err.println("" + (fileProperties.conjectureNum - conjNum) +
                                      " conjectures left")

                  prover match {
                    case prover : ParallelFileProver =>
                      // reorder strategies, to start with the one that
                      // worked last time
                      rawStrategies =
                        rawStrategies(prover.successfulProverNum) ::
                        (rawStrategies take prover.successfulProverNum) :::
                        (rawStrategies drop (prover.successfulProverNum + 1))
                    case _ => // nothing
                  }
                }
                case _ =>
                  result = prover.result
              }
            }

            // if we have already printed a preliminary result, we
            // only check whether we know have a certificate to show
            if (prelResultPrinted == null) {
              printResult(result, prover, settings2, lastFilename)
            } else result match {
              case Prover.NoCounterModelCert(cert) => 
                printCertificate(cert, settings, prover, lastFilename)
              case Prover.NoCounterModelCertInter(cert, inters) =>
                printCertificate(cert, settings, prover, lastFilename)
              case _ =>
                // nothing
            }
            
            val timeAfter = System.currentTimeMillis
            
            Console.withOut(Console.err) {
              println
              if (Param.LOGO(settings))
                println("" + (timeAfter - timeBefore) + "ms")
            }
            
/*
            prover match {
              case prover : AbstractFileProver => {
                printSMT(prover, name, settings)
                printTPTP(prover, name, settings)
              }
              case _ => // nothing
            }
*/
            
            /* println
            println(ap.util.Timer)
            ap.util.Timer.reset */
            
            Some(result)
          } catch {
      case _ : StackOverflowError => {
        format match {
          case Param.InputFormat.SMTLIB => {
            println("unknown")
            Console.err.println("Stack overflow, giving up")
          }
          case Param.InputFormat.TPTP => {
            println("% SZS status GaveUp for " + lastFilename)
            Console.err.println("Stack overflow, giving up")
          }
          case _ =>
            println("Stack overflow, giving up")
        }
        // let's hope that everything is still in a valid state
        None
      }
      case _ : OutOfMemoryError => {
        format match {
          case Param.InputFormat.SMTLIB => {
            println("unknown")
            Console.err.println("Out of memory, giving up")
          }
          case Param.InputFormat.TPTP => {
            println("% SZS status GaveUp for " + lastFilename)
            Console.err.println("Out of memory, giving up")
          }
          case _ =>
            println("Out of memory, giving up")
        }
        System.gc
        // let's hope that everything is still in a valid state
        None
      }
      case e : Throwable => {
        format match {
          case Param.InputFormat.SMTLIB => {
            println("error")
            Console.err.println(e.getMessage) 
          }
          case Param.InputFormat.TPTP => {
            e match {
              case _ : GaveUpException =>
                println("% SZS status GaveUp for " + lastFilename)
              case _ =>
                println("% SZS status Error for " + lastFilename)
            }
            Console.err.println(e.getMessage) 
          }
          case _ => {
            println("ERROR: " + e.getMessage)
          }
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
                           Param.GENERATE_TOTALITY_AXIOMS(settings) ==
                           Param.TotalityAxiomOptions.All) { p =>
      val parser = SMTParser2InputAbsy(settings.toParserSettings, p)
      parser.processIncrementally(input,
                                  Param.TIMEOUT(settings),
                                  Param.TIMEOUT_PER(settings),
                                  userDefStoppingCond)
    }

/*
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
*/
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
//         e.printStackTrace
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
  
  def printResult(result : Prover.Result,
                  prover : Prover,
                  settings : GlobalSettings,
                  lastFilename : String)
                 (implicit format : Param.InputFormat.Value) = format match {
    case Param.InputFormat.SMTLIB => result match {
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
              case Prover.MaybeCounterModel(model) =>  {
                println("unknown")
                Console.withOut(Console.err) {
                  println
                  println("Possible model:")
                  printFormula(model)
                }
              }
              case Prover.NoCounterModel =>  {
                println("unsat")
              }
              case Prover.NoCounterModelCert(cert) =>  {
                println("unsat")
                printCertificate(cert, settings, prover, lastFilename)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                println("unsat")
                printCertificate(cert, settings, prover, lastFilename)
                Console.err.println
                Console.err.println("Interpolants:")
                for (i <- inters) printFormula(i)
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

    case Param.InputFormat.TPTP | Param.InputFormat.Princess => {
            val fileProperties = Param.FILE_PROPERTIES(settings)
            result match {
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
                
                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
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
                
                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
              }
              case Prover.NoProof(tree) => {
                Console.err.println("UNKNOWN")
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
                println("% SZS status " + fileProperties.negativeResult + " for " + lastFilename)
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
                
                println("% SZS status " + fileProperties.negativeResult + " for " + lastFilename)
              }
              case Prover.MaybeCounterModel(model) =>  {
                Console.withOut(Console.err) {
                model match {
                  case IBoolLit(true) => // nothing
                  case _ => {
                    println
                    println("Possible countermodel:")
                    printFormula(model)
                  }
                }
                }
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("false")
                }
                println("% SZS status GaveUp for " + lastFilename)
              }
              case Prover.NoCounterModel =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }
                
                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
              }
              case Prover.NoCounterModelCert(cert) =>  {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }

                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
                printCertificate(cert, settings, prover, lastFilename)
              }
              case Prover.NoCounterModelCertInter(cert, inters) => {
                Console.err.println("No countermodel exists, formula is valid")
                if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
                  println
                  println("Most-general constraint:")
                  println("true")
                }

                Console.withOut(Console.err) {
                  println
                  println("Interpolants:")
                  for (i <- inters) printFormula(i)
                }

                printCertificate(cert, settings, prover, lastFilename)
                
                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
              }
              case Prover.Model(model) =>  {
                Console.withOut(Console.err) {
                  println("Formula is valid, satisfying assignment for the existential constants is:")
                  printFormula(model)
                }
                println("% SZS status " + fileProperties.positiveResult + " for " + lastFilename)
              }
              case Prover.NoModel =>  {
                Console.err.println("No satisfying assignment for the existential constants exists, formula is invalid")
                println("% SZS status " + fileProperties.negativeResult + " for " + lastFilename)
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
