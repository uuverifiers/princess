/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import ap.parameters._
import ap.parser.{InputAbsy2Internal,
                  ApParser2InputAbsy, SMTParser2InputAbsy, TPTPTParser,
                  Preprocessing,
                  FunctionEncoder, IExpression, INamedPart, PartName,
                  IFunction, IInterpolantSpec, IBinJunctor, Environment}
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher}
import ap.terfor.preds.Predicate
import ap.theories.{Theory, TheoryRegistry}
import ap.proof.{ModelSearchProver, ExhaustiveCCUProver, ConstraintSimplifier}
import ap.proof.tree.ProofTree
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.Certificate
import ap.proof.theoryPlugins.PluginSequence
import ap.util.{Debug, Timeout, Seqs}

object AbstractFileProver {
  
  private val AC = Debug.AC_MAIN
  
}

abstract class AbstractFileProver(reader : java.io.Reader, output : Boolean,
                                  timeout : Int, userDefStoppingCond : => Boolean,
                                  settings : GlobalSettings) extends Prover {

  private val startTime = System.currentTimeMillis

  private val stoppingCond = () => {
    if ((System.currentTimeMillis - startTime > timeout) || userDefStoppingCond)
      Timeout.raise
  }

  protected def println(str : => String) : Unit =
    if (output) Predef.println(str)
  
  protected def print(str : => String) : Unit =
    if (output) Predef.print(str)
  
  private def newParser = Param.INPUT_FORMAT(settings) match {
    case Param.InputFormat.Princess => ApParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.SMTLIB => SMTParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.TPTP => TPTPTParser(settings.toParserSettings)
  }
  
  val (inputFormulas, originalInputFormula,
       interpolantSpecs, signature, gcedFunctions, functionEncoder) = {
    val parser = newParser
    val (preF, interpolantSpecs, preSignature) = parser(reader)
    reader.close


    // HACK: currently the Groebner theories does not support interpolation,
    // if necessary switch to bit-shift multiplication
    val (f, signature) =
      if ((preSignature.theories contains ap.theories.nia.GroebnerMultiplication) &&
          (Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
            case Param.ProofConstructionOptions.Never => false
            case Param.ProofConstructionOptions.Always => true
            case Param.ProofConstructionOptions.IfInterpolating => !interpolantSpecs.isEmpty
           })) {
        Console.withOut(Console.err) {
          println("Warning: switching to " + ap.theories.BitShiftMultiplication +
                  " for proof construction")
        }
        (ap.theories.BitShiftMultiplication convert preF,
         preSignature addTheories List(ap.theories.BitShiftMultiplication))
      } else {
        (preF, preSignature)
      }

    
    val preprocSettings = settings.toPreprocessingSettings

    Console.withOut(Console.err) {
      println("Preprocessing ...")
    }
    
    val functionEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings))
    for (t <- signature.theories)
      functionEnc addTheory t

    val (inputFormulas, interpolantS, sig) =
      Preprocessing(f, interpolantSpecs, signature, preprocSettings, functionEnc)
    
    val gcedFunctions = Param.FUNCTION_GC(settings) match {
      case Param.FunctionGCOptions.None =>
        Set[Predicate]()
      case Param.FunctionGCOptions.Total =>
        (for ((p, f) <- functionEnc.predTranslation.iterator; if (!f.partial))
          yield p).toSet
      case Param.FunctionGCOptions.All =>
        functionEnc.predTranslation.keySet.toSet
    }
    
    val oriFormula =
      // only store unprocessed input formula if we plan to print it later
      if (Param.PRINT_SMT_FILE(settings) != "" ||
          Param.PRINT_TPTP_FILE(settings) != "")  f else null

    (inputFormulas, oriFormula, interpolantS, sig, gcedFunctions, functionEnc)
  }
  
  protected val theories = signature.theories

  val functionalPreds = 
    (for ((p, f) <- functionEncoder.predTranslation.iterator;
          if (!f.relational)) yield p).toSet
  
  val predicateTranslation =
    functionEncoder.predTranslation.toMap

  private val plugin =
    PluginSequence(for (t <- theories; p <- t.plugin.toSeq) yield p)

  private val constructProofs = Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
    case Param.ProofConstructionOptions.Never => false
    case Param.ProofConstructionOptions.Always => true
    case Param.ProofConstructionOptions.IfInterpolating => !interpolantSpecs.isEmpty
  }

  val order = signature.order

  private val theoryAxioms =
    Conjunction.conj(for (t <- theories) yield t.axioms, order).negate

  private val reducer =
    ReduceWithConjunction(Conjunction.TRUE, functionalPreds, false, order)

  private val allPartNames =
    (List(PartName.NO_NAME) ++
     (for (INamedPart(n, _) <- inputFormulas) yield n)).distinct

  val (namedParts, formulas, matchedTotalFunctions, ignoredQuantifiers) = {
    var ignoredQuantifiers = false

    /**
     * In some cases, convert universal quantifiers to existential ones.
     * At the moment, this is in particular necessary when constructing
     * proof for interpolation.
     */
    def convertQuantifiers(c : Conjunction) : Conjunction =
      if (/* constructProofs || */ Param.IGNORE_QUANTIFIERS(settings)) {
        val withoutQuans =
          IterativeClauseMatcher.convertQuantifiers(
            c, signature.predicateMatchConfig, false)
        if (!ignoredQuantifiers && !(withoutQuans eq c)) {
          Console.err.println("Warning: ignoring some quantifiers")
          ignoredQuantifiers = true
        }
        withoutQuans
      } else {
        IterativeClauseMatcher.pullOutTriggers(
          c, signature.predicateMatchConfig)
      }

    if (constructProofs) {
      // keep the different formula parts separate
      val rawNamedParts =
        Map(PartName.NO_NAME -> Conjunction.FALSE) ++
        (for (INamedPart(n, f) <- inputFormulas.iterator)
         yield (n -> Conjunction.conj(InputAbsy2Internal(f, order), order)))
      val reducedNamedParts =
        for ((n, c) <- rawNamedParts) yield n match {
          case PartName.NO_NAME =>
            (PartName.NO_NAME ->
             convertQuantifiers(
               reducer(Conjunction.disj(List(theoryAxioms, c), order))))
          case n =>
            (n -> convertQuantifiers(reducer(c)))
        }

      (reducedNamedParts,
       for (n <- allPartNames) yield reducedNamedParts(n),
       checkMatchedTotalFunctions(rawNamedParts map (_._2)),
       ignoredQuantifiers)
    } else {
      // merge everything into one formula
      val rawF =
        InputAbsy2Internal(
          IExpression.or(for (f <- inputFormulas.iterator)
                         yield (IExpression removePartName f)), order)
      val f = convertQuantifiers(
                reducer(Conjunction.disjFor(List(theoryAxioms, rawF), order)))
      (Map(PartName.NO_NAME -> f),
       List(f),
       checkMatchedTotalFunctions(List(Conjunction.conj(rawF, order))),
       ignoredQuantifiers)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  protected val goalSettings = {
    var gs = settings.toGoalSettings

    gs = Param.ASSUME_INFINITE_DOMAIN.set(gs, false)

    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, gcedFunctions)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs = Param.SINGLE_INSTANTIATION_PREDICATES.set(gs,
           (for (t <- theories.iterator;
                 p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
    gs = Param.PREDICATE_MATCH_CONFIG.set(gs, signature.predicateMatchConfig)
    gs = Param.THEORY_PLUGIN.set(gs, plugin)
    gs = Param.NAME_PROVIDER.set(gs, new Param.NameProvider)
    gs
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
  
  //////////////////////////////////////////////////////////////////////////////

  protected lazy val formulaConstants =
    (for (f <- formulas.iterator; c <- f.constants.iterator) yield c).toSet
  protected lazy val formulaQuantifiers =
    (for (f <- formulas.iterator;
          q <- Conjunction.collectQuantifiers(f).iterator) yield q).toSet

  protected lazy val canUseModelSearchProver = {
    val config = Param.PREDICATE_MATCH_CONFIG(goalSettings)

    (formulas exists (_.isTrue)) ||
    (Seqs.disjoint(formulaConstants, signature.existentialConstants) &&
     (if (Param.POS_UNIT_RESOLUTION(goalSettings))
        formulas forall (IterativeClauseMatcher isMatchableRec(_, config))
      else
        (formulaQuantifiers subsetOf Set(Quantifier.ALL))))
  }

  //////////////////////////////////////////////////////////////////////////////

  private def checkMatchedTotalFunctions(conjs : Iterable[Conjunction]) : Boolean =
    Param.POS_UNIT_RESOLUTION(settings) && {
      val config = signature.predicateMatchConfig
      conjs exists { c =>
        IterativeClauseMatcher.matchedPredicatesRec(c, config) exists {
          p => (functionEncoder.predTranslation get p) match {
                 case Some(f) => !f.partial
                 case None => false
               }
        }
      }
    }

  private lazy val getSatSoundnessConfig : Theory.SatSoundnessConfig.Value =
    if (!canUseModelSearchProver || matchedTotalFunctions)
      Theory.SatSoundnessConfig.General
    else if (formulas forall (_.predicates.isEmpty))
      Theory.SatSoundnessConfig.Elementary
    else
      Theory.SatSoundnessConfig.Existential

  private lazy val theoriesAreSatComplete =
    theories.isEmpty || {
      val config = getSatSoundnessConfig
      Param.POS_UNIT_RESOLUTION(goalSettings) &&
      (theories exists (_.isSoundForSat(theories, config)))
    }

  private lazy val allFunctionsArePartial =
    (formulas forall { f => f.predicates forall {
       p => (functionEncoder.predTranslation get p) match {
               case Some(f) => f.partial
               case None => true
             }
     }}) &&
    (theories forall { t => t.functions forall (_.partial) })

  protected lazy val soundForSat =
    !ignoredQuantifiers &&
    theoriesAreSatComplete &&
    (!matchedTotalFunctions ||
     Param.GENERATE_TOTALITY_AXIOMS(settings) ||
// not quite clear yet how this trigger strategy should be integrated
//     Param.TRIGGER_GENERATION(settings) ==
//       Param.TriggerGenerationOptions.CompletenessPreserving ||
     allFunctionsArePartial)

  //////////////////////////////////////////////////////////////////////////////

  protected def findModelTimeout : Either[Conjunction, Certificate] = {
    Console.withOut(Console.err) {
      println("Constructing satisfying assignment for the existential constants ...")
    }
    findCounterModelTimeout(List(Conjunction.disj(formulas, order).negate))
  }
  
  protected def findCounterModelTimeout : Either[Conjunction, Certificate] = {
    Console.withOut(Console.err) {
      println("Constructing countermodel ...")
    }
    findCounterModelTimeout(if (formulas exists (_.isTrue))
                              List(Conjunction.TRUE)
                            else
                              formulas)
  }
  
  protected def findCounterModelTimeout(f : Seq[Conjunction]) =
    Timeout.withChecker(stoppingCond) {
      ModelSearchProver(f, order, goalSettings)
    }
  
  protected def findModel(f : Conjunction) : Conjunction =
    ModelSearchProver(f.negate, f.order)
  
  protected def constructProofTree : (ProofTree, Boolean, Certificate) = {
    // explicitly quantify all universal variables
    
    val closedFor = Conjunction.quantify(Quantifier.ALL,
                                         order sort signature.nullaryFunctions,
                                         Conjunction.disj(formulas, order), order)
    
    Console.withOut(Console.err) {
      println("Proving ...")
    }
    
    Timeout.withChecker(stoppingCond) {
      val prover =
        new ExhaustiveCCUProver(!Param.MOST_GENERAL_CONSTRAINT(settings), goalSettings)
      val tree = Console.withErr(ap.CmdlMain.NullStream) { prover(closedFor, signature) }
      val validConstraint = tree.ccUnifiable
         // prover.isValidConstraint(tree.closingConstraint, signature)
      (tree, validConstraint,
       if (validConstraint && constructProofs)
         prover extractCertificate tree
       else
         null)
    }
  }
}
