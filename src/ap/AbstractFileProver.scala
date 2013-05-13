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

import ap.parameters._
import ap.parser.{InputAbsy2Internal,
                  ApParser2InputAbsy, SMTParser2InputAbsy, TPTPTParser,
                  Preprocessing,
                  FunctionEncoder, IExpression, INamedPart, IFunction,
                  IInterpolantSpec, IBinJunctor, Environment}
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher}
import ap.terfor.preds.Predicate
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier}
import ap.proof.tree.ProofTree
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.Certificate
import ap.util.{Debug, Timeout}

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
                                           env : Environment[CT,VT,PT,FT])
                                          : Set[IFunction] =
    Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None => Set()
      case Param.TriggerGenerationOptions.All => env.nonNullaryFunctions
      case Param.TriggerGenerationOptions.Total =>
        for (f <- env.nonNullaryFunctions; if (!f.partial && !f.relational))
          yield f
    }
  
  private def newParser = Param.INPUT_FORMAT(preSettings) match {
    case Param.InputFormat.Princess => ApParser2InputAbsy(preSettings.toParserSettings)
    case Param.InputFormat.SMTLIB => SMTParser2InputAbsy(preSettings.toParserSettings)
    case Param.InputFormat.TPTP => TPTPTParser(preSettings.toParserSettings)
  }
  
  import CmdlMain.domain_size
  
  val (inputFormulas, interpolantSpecs, signature, gcedFunctions, functionEncoder,
       settings) = {
    val parser = newParser
    val (f, interpolantSpecs, preSignature) = parser(reader)
    reader.close

    val settings = parser match {
      case parser : TPTPTParser =>
        Param.FINITE_DOMAIN_CONSTRAINTS.set(preSettings,
                                            parser.chosenFiniteConstraintMethod)
      case _ =>
        preSettings
    }
    
    val signature = Param.FINITE_DOMAIN_CONSTRAINTS(settings) match {
      case Param.FiniteDomainConstraints.DomainSize =>
        new Signature(preSignature.universalConstants + domain_size,
                      preSignature.existentialConstants,
                      preSignature.nullaryFunctions,
                      preSignature.order.extend(domain_size, Set()),
                      preSignature.domainPredicates,
                      preSignature.functionTypes)
      case _ =>
        preSignature
    }
    
    val preprocSettings = {
      var ps = settings.toPreprocessingSettings
      ps = Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(ps,
             determineTriggerGenFunctions(settings, parser.env))
      ps = Param.DOMAIN_PREDICATES.set(ps, signature.domainPredicates)
      ps
    }
    
    Console.withOut(Console.err) {
      println("Preprocessing ...")
    }
    
    val functionEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings),
                           signature.functionTypes)
    
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
    
    (inputFormulas, interpolantS, sig, gcedFunctions, functionEnc, settings)
  }

  private val functionalPreds = 
    (for ((p, f) <- functionEncoder.predTranslation.iterator;
          if (!f.relational)) yield p).toSet
  
  private val constructProofs = Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
    case Param.ProofConstructionOptions.Never => false
    case Param.ProofConstructionOptions.Always => true
    case Param.ProofConstructionOptions.IfInterpolating => !interpolantSpecs.isEmpty
  }
    
  val order = signature.order

  private val reducer =
    ReduceWithConjunction(Conjunction.TRUE, functionalPreds,
                          Param.FINITE_DOMAIN_CONSTRAINTS.assumeInfiniteDomain(settings),
                          order)
  
  val formulas =
    if (constructProofs)
      // keep the different formula parts separate
      for (f <- inputFormulas) yield
        reducer(
          Conjunction.conj(InputAbsy2Internal(IExpression removePartName f, order),
                           order))
    else
      // merge everything into one formula
      List(reducer(Conjunction.conj(InputAbsy2Internal(
          IExpression.connect(for (f <- inputFormulas.iterator)
                                yield (IExpression removePartName f),
                              IBinJunctor.Or), order), order)))
      
  //////////////////////////////////////////////////////////////////////////////
  
  protected val goalSettings = {
    var gs = settings.toGoalSettings
    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, gcedFunctions)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
    gs = Param.DOMAIN_PREDICATES.set(gs, signature.domainPredicates)
    gs = Param.PREDICATE_MATCH_CONFIG.set(gs,
        (for (p <- signature.domainPredicates.iterator)
         yield (p -> IterativeClauseMatcher.PredicateMatchStatus.None)).toMap)
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

  lazy val namedParts =
    Map() ++ (for ((INamedPart(name, _), f) <-
                   inputFormulas.iterator zip formulas.iterator)
              yield (name -> f))
  
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
