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
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher}
import ap.terfor.preds.Predicate
import ap.theories.{Theory, TheoryRegistry}
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier}
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
                                  preSettings : GlobalSettings) extends Prover {

  private val startTime = System.currentTimeMillis

  private val stoppingCond = () => {
    if ((System.currentTimeMillis - startTime > timeout) || userDefStoppingCond)
      Timeout.raise
  }

  protected def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  private def determineTriggerGenFunctions[CT,VT,PT,FT]
                                          (settings : GlobalSettings,
                                           env : Environment[CT,VT,PT,FT],
                                           signature : Signature)
                                          : Set[IFunction] =
    Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None => Set()
      case Param.TriggerGenerationOptions.All =>
        env.nonNullaryFunctions ++ (
          for (t <- signature.theories.iterator;
               f <- t.triggerRelevantFunctions.iterator) yield f)
      case Param.TriggerGenerationOptions.Total =>
        ((for (f <- env.nonNullaryFunctions.iterator;
               if (!f.partial && !f.relational)) yield f) ++ (
          for (t <- signature.theories.iterator;
               f <- t.triggerRelevantFunctions.iterator) yield f)).toSet
    }
  
  private def newParser = Param.INPUT_FORMAT(preSettings) match {
    case Param.InputFormat.Princess => ApParser2InputAbsy(preSettings.toParserSettings)
    case Param.InputFormat.SMTLIB => SMTParser2InputAbsy(preSettings.toParserSettings)
    case Param.InputFormat.TPTP => {
      val settings = Param.MAKE_QUERIES_PARTIAL.set(
                       preSettings.toParserSettings,
                       Param.GENERATE_TOTALITY_AXIOMS(preSettings) ==
                         Param.TotalityAxiomOptions.Ctors)
      TPTPTParser(settings)
    }
  }
  
  import CmdlMain.domain_size
  
  val (inputFormulas, originalInputFormula,
       interpolantSpecs, signature, gcedFunctions, functionEncoder,
       settings) = {
    val parser = newParser
    val (preF, interpolantSpecs, preSignature) = parser(reader)
    reader.close

    val settings = parser match {
      case parser : TPTPTParser =>
        Param.FINITE_DOMAIN_CONSTRAINTS.set(preSettings,
                                            parser.chosenFiniteConstraintMethod)
      case _ =>
        preSettings
    }

    // HACK: currently the Groebner theories does not support interpolation,
    // if necessary switch to bit-shift multiplication
    val (f, preSignature2) =
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

    val signature = Param.FINITE_DOMAIN_CONSTRAINTS(settings) match {
      case Param.FiniteDomainConstraints.DomainSize =>
        Signature(preSignature2.universalConstants + domain_size,
                  preSignature2.existentialConstants,
                  preSignature2.nullaryFunctions,
                  preSignature2.predicateMatchConfig,
                  preSignature2.order.extend(domain_size, Set()),
                  preSignature2.domainPredicates,
                  preSignature2.functionTypes)
      case _ =>
        preSignature2
    }
    
    val preprocSettings = {
      var ps = settings.toPreprocessingSettings
      ps = Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(ps,
             determineTriggerGenFunctions(settings, parser.env, signature))
      ps = Param.DOMAIN_PREDICATES.set(ps, signature.domainPredicates)
      ps
    }
    
    Console.withOut(Console.err) {
      println("Preprocessing ...")
    }
    
    val functionEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings) !=
                             Param.TotalityAxiomOptions.None,
                           signature.functionTypes)
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

    (inputFormulas, oriFormula, interpolantS, sig, gcedFunctions, functionEnc, settings)
  }

  protected val theories = signature.theories

  private val functionalPreds = 
    (for ((p, f) <- functionEncoder.predTranslation.iterator;
          if (!f.relational)) yield p).toSet
  
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
    ReduceWithConjunction(Conjunction.TRUE, functionalPreds,
                          Param.FINITE_DOMAIN_CONSTRAINTS.assumeInfiniteDomain(settings),
                          order)

  private val allPartNames =
    (List(PartName.NO_NAME) ++
     (for (INamedPart(n, _) <- inputFormulas) yield n)).distinct

  val (namedParts, formulas, matchedTotalFunctions) =
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
             reducer(Conjunction.disj(List(theoryAxioms, c), order)))
          case n =>
            (n -> reducer(c))
        }

      (reducedNamedParts,
       for (n <- allPartNames) yield reducedNamedParts(n),
       checkMatchedTotalFunctions(rawNamedParts map (_._2)))
    } else {
      // merge everything into one formula
      val rawF =
        InputAbsy2Internal(
          IExpression.or(for (f <- inputFormulas.iterator)
                         yield (IExpression removePartName f)), order)
      val f = reducer(Conjunction.disjFor(List(theoryAxioms, rawF), order))
      (Map(PartName.NO_NAME -> f),
       List(f),
       checkMatchedTotalFunctions(List(Conjunction.conj(rawF, order))))
    }

  //////////////////////////////////////////////////////////////////////////////
  
  protected val goalSettings = {
    var gs = settings.toGoalSettings
    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, gcedFunctions)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs = Param.DOMAIN_PREDICATES.set(gs, signature.domainPredicates)
    gs = Param.SINGLE_INSTANTIATION_PREDICATES.set(gs,
           (for (t <- theories.iterator;
                 p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
    gs = Param.PREDICATE_MATCH_CONFIG.set(gs, signature.predicateMatchConfig)
    gs = Param.THEORY_PLUGIN.set(gs, plugin)
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
    theoriesAreSatComplete &&
    (Param.GENERATE_TOTALITY_AXIOMS(settings) == Param.TotalityAxiomOptions.All ||
     !matchedTotalFunctions ||
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
  
  protected def constructProofTree : (ProofTree, Boolean) = {
    // explicitly quantify all universal variables
    
    val closedFor = Conjunction.quantify(Quantifier.ALL,
                                         order sort signature.nullaryFunctions,
                                         Conjunction.disj(formulas, order), order)
    
    Console.withOut(Console.err) {
      println("Proving ...")
    }
    
    Timeout.withChecker(stoppingCond) {
      val prover =
        new ExhaustiveProver(!Param.MOST_GENERAL_CONSTRAINT(settings), goalSettings)
      val tree = prover(closedFor, signature)
      val validConstraint = prover.isValidConstraint(tree.closingConstraint, signature)
      (tree, validConstraint)
    }
  }
}
