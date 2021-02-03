/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2021 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.parameters._
import ap.parser._
import ap.interpolants.ArraySimplifier
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher, SeqReducerPluginFactory}
import ap.terfor.preds.Predicate
import ap.theories.{Theory, TheoryRegistry, Incompleteness}
import ap.types.{TypeTheory, IntToTermTranslator}
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier,
                 QuantifierElimProver}
import ap.proof.tree.{ProofTree, SeededRandomDataSource}
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.{Certificate, CertFormula}
import ap.proof.theoryPlugins.PluginSequence
import ap.util.{Debug, Timeout, Seqs}

object AbstractFileProver {
  
  private val AC = Debug.AC_MAIN

  private def determineSimplifier(settings : GlobalSettings)
                                 : ConstraintSimplifier =
    Param.SIMPLIFY_CONSTRAINTS(settings) match {
      case Param.ConstraintSimplifierOptions.None =>
        ConstraintSimplifier.NO_SIMPLIFIER
      case x =>
        ConstraintSimplifier(x == Param.ConstraintSimplifierOptions.Lemmas,
                             Param.DNF_CONSTRAINTS(settings),
                             Param.TRACE_CONSTRAINT_SIMPLIFIER(settings))
    }

  protected[ap] def filterNonTheoryParts(model : Conjunction) : Conjunction = {
    implicit val _ = model.order
    val remainingPredConj = model.predConj filter {
      a => (TheoryRegistry lookupSymbol a.pred).isEmpty
    }
    model.updatePredConj(remainingPredConj)
  }
}

abstract class AbstractFileProver(reader : java.io.Reader, output : Boolean,
                                  timeout : Int, userDefStoppingCond : => Boolean,
                                  settings : GlobalSettings) extends Prover {

  import AbstractFileProver._

  private val startTime = System.currentTimeMillis

  private val stoppingCond = () => {
    if ((System.currentTimeMillis - startTime > timeout) || userDefStoppingCond)
      Timeout.raise
  }

  protected def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  private def newParser = Param.INPUT_FORMAT(settings) match {
    case Param.InputFormat.Princess =>
      ApParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.SMTLIB =>
      SMTParser2InputAbsy(settings.toParserSettings)
    case Param.InputFormat.TPTP =>
      TPTPTParser(settings.toParserSettings)
  }

  //////////////////////////////////////////////////////////////////////////////

  // Raw data produced by the parser
  val (rawInputFormula, rawInterpolantSpecs, rawSignature) = {
    val parser = newParser
    val (f, interpolantSpecs, signature) = parser(reader)
    reader.close
    (f, interpolantSpecs, signature)
  }

  val constructProofs = Param.PROOF_CONSTRUCTION_GLOBAL(settings) match {
    case Param.ProofConstructionOptions.Never =>
      false
    case Param.ProofConstructionOptions.Always =>
      true
    case Param.ProofConstructionOptions.IfInterpolating =>
      !rawInterpolantSpecs.isEmpty ||
      Param.COMPUTE_UNSAT_CORE(settings) ||
      Param.PRINT_CERTIFICATE(settings) ||
      Param.PRINT_DOT_CERTIFICATE_FILE(settings) != ""
  }

  lazy val rawConstants : scala.collection.Set[ConstantTerm] =
    SymbolCollector constants rawInputFormula

  lazy val rawQuantifiers : Set[Quantifier] =
    QuantifierCollectingVisitor(rawInputFormula)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class taking care of pre-processing, and translation to
   * internal data-structures.
   */
  protected class Translation(rawFormula : IFormula,
                              settings : GlobalSettings) {
    val (inputFormulas, preprocInterpolantSpecs, transSignature,
         gcedFunctions, functionEncoder, incompletePreproc) = {
      var incompletePreproc = false
  
      val preprocSettings = settings.toPreprocessingSettings
  
      Console.withOut(Console.err) {
        println("Preprocessing ...")
      }
      
      val genTotality =
        Param.GENERATE_TOTALITY_AXIOMS(settings) &&
        !IsUniversalFormulaVisitor(rawFormula)
  
      val functionEnc =
        new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings), genTotality)
      for (t <- rawSignature.theories)
        functionEnc addTheory t
  
      val ((inputFormulas, interpolantS, sig), incomp) = Incompleteness.track {
        Preprocessing(rawFormula, rawInterpolantSpecs,
                      rawSignature, preprocSettings, functionEnc)
      }

      if (incomp)
        incompletePreproc = true
      
      val sig2 =
        if (sig.isSorted) {
  //        Console.withOut(Console.err) {
  //          println("Warning: adding theory of types")
  //        }
          sig.addTheories(List(ap.types.TypeTheory), true)
        } else {
          sig
        }
  
      val gcedFunctions = Param.FUNCTION_GC(settings) match {
        case Param.FunctionGCOptions.None =>
          Set[Predicate]()
        case Param.FunctionGCOptions.Total =>
          (for ((p, f) <- functionEnc.predTranslation.iterator;
                if !f.partial && (TheoryRegistry lookupSymbol f).isEmpty)
           yield p).toSet
        case Param.FunctionGCOptions.All =>
          (for (p <- functionEnc.predTranslation.keySet.iterator;
                if (TheoryRegistry lookupSymbol p).isEmpty)
           yield p).toSet
      }
      
      (inputFormulas, interpolantS, sig2, gcedFunctions, functionEnc,
       incompletePreproc)
    }
  
    val theories = transSignature.theories
    val order = transSignature.order
  
    private val theoryAxioms =
      Conjunction.conj(for (t <- theories) yield t.axioms, order).negate
    
    private val functionalPreds = 
      (for ((p, f) <- functionEncoder.predTranslation.iterator;
            if (!f.relational)) yield p).toSet
    
    private val reducerSettings = {
      var rs = settings.toReducerSettings
      rs = Param.FUNCTIONAL_PREDICATES.set(
           rs, functionalPreds)
      rs = Param.REDUCER_PLUGIN.set(
           rs, SeqReducerPluginFactory(for (t <- theories) yield t.reducerPlugin))
      rs
    }
  
    ////////////////////////////////////////////////////////////////////////////

    val (namedParts, formulas, matchedTotalFunctions, ignoredQuantifiers2) = {
      var ignoredQuantifiers = false
  
      val reducer =
        ReduceWithConjunction(Conjunction.TRUE, order, reducerSettings)
      val allPartNames =
        (List(PartName.NO_NAME) ++
         (for (INamedPart(n, _) <- inputFormulas) yield n)).distinct
  
      /**
       * In some cases, convert universal quantifiers to existential ones.
       * At the moment, this is in particular necessary when constructing
       * proof for interpolation.
       */
      def convertQuantifiers(c : Conjunction) : Conjunction =
        if (constructProofs || Param.IGNORE_QUANTIFIERS(settings)) {
          val withoutQuans =
            IterativeClauseMatcher.convertQuantifiers(
              c, transSignature.predicateMatchConfig)
          if (!ignoredQuantifiers && !(withoutQuans eq c)) {
            Console.err.println("Warning: ignoring some quantifiers")
            ignoredQuantifiers = true
          }
          withoutQuans
        } else {
          c
        }
  
      if (constructProofs) {
        // keep the different formula parts separate
        val rawNamedParts =
          Map(PartName.NO_NAME -> Conjunction.FALSE) ++
          (for (INamedPart(n, f) <- inputFormulas.iterator)
           yield (n -> Conjunction.conj(InputAbsy2Internal(f, order), order)))
        val reducedNamedParts =
          for ((n, c) <- rawNamedParts) yield {
            val (redC, incomp) = Incompleteness.track {
              Theory.preprocess(reducer(c), transSignature.theories, order)
            }
  
            if (incomp)
              ignoredQuantifiers = true
  
            n match {
              case PartName.NO_NAME =>
                (PartName.NO_NAME ->
                  convertQuantifiers(
                    Conjunction.disj(List(theoryAxioms, redC), order)))
              case n =>
                (n -> convertQuantifiers(redC))
            }
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
        val (redF, incomp) = Incompleteness.track {
          Theory.preprocess(reducer(Conjunction.conj(rawF, order)),
                            transSignature.theories, order)
        }
  
        if (incomp)
          ignoredQuantifiers = true
  
        val f =
          convertQuantifiers(Conjunction.disj(List(theoryAxioms, redF), order))
  
        (Map(PartName.NO_NAME -> f),
         List(f),
         checkMatchedTotalFunctions(List(Conjunction.conj(rawF, order))),
         ignoredQuantifiers)
      }
    }

    val ignoredQuantifiers = incompletePreproc || ignoredQuantifiers2

    private def checkMatchedTotalFunctions(conjs : Iterable[Conjunction])
                                          : Boolean =
      Param.POS_UNIT_RESOLUTION(settings) && {
        val config = transSignature.predicateMatchConfig
        conjs exists { c =>
          IterativeClauseMatcher.matchedPredicatesRec(c, config) exists {
            p => (functionEncoder.predTranslation get p) match {
                   case Some(f) => !f.partial
                   case None => false
                 }
          }
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    def getAssumedFormulaParts(cert : Certificate) : Set[PartName] = {
      val assumed = cert.assumedFormulas
      (for ((n, f) <- namedParts.iterator;
            if (assumed contains CertFormula(f.negate)))
       yield n).toSet
    }

    def getFormulaParts : Map[PartName, Conjunction] =
      namedParts

    def getPredTranslation : Map[Predicate, IFunction] =
      functionEncoder.predTranslation.toMap

    val goalSettings = {
      var gs = settings.toGoalSettings
      gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
      gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
      gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
      gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, gcedFunctions)
      gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
      gs = Param.SINGLE_INSTANTIATION_PREDICATES.set(gs,
           (for (t <- theories.iterator;
                 p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
      gs = Param.PREDICATE_MATCH_CONFIG.set(gs, transSignature.predicateMatchConfig)
      val plugin =
        PluginSequence(for (t <- theories; p <- t.plugin.toSeq) yield p)
      gs = Param.THEORY_PLUGIN.set(gs, plugin)
      for (seed <- Param.RANDOM_SEED(settings))
        gs = Param.RANDOM_DATA_SOURCE.set(gs, new SeededRandomDataSource(seed))
      gs = Param.REDUCER_SETTINGS.set(gs, reducerSettings)
      gs
    }

    ////////////////////////////////////////////////////////////////////////////

    lazy val formulaConstants =
      (for (f <- formulas.iterator; c <- f.constants.iterator) yield c).toSet
    lazy val formulaQuantifiers =
      (for (f <- formulas.iterator;
            q <- Conjunction.collectQuantifiers(f).iterator) yield q).toSet

    lazy val canUseModelSearchProver = {
      val config = Param.PREDICATE_MATCH_CONFIG(goalSettings)

      (!Param.COMPUTE_MODEL(settings) ||
       transSignature.existentialConstants.isEmpty) &&
      ((formulas exists (_.isTrue)) ||
       (Seqs.disjoint(rawConstants, transSignature.existentialConstants) &&
        (if (Param.POS_UNIT_RESOLUTION(goalSettings))
           formulas forall (IterativeClauseMatcher isMatchableRec(_, config))
         else
           (formulaQuantifiers subsetOf Set(Quantifier.ALL)))))
    }


    ////////////////////////////////////////////////////////////////////////////

    private lazy val getSatSoundnessConfig : Theory.SatSoundnessConfig.Value =
      // TODO: this does not really capture the case where we use
      // the model-search prover, but also e-matching to instantiate
      // quantified axioms (and not just functional consistency)
      if (!canUseModelSearchProver /* || matchedTotalFunctions */)
        Theory.SatSoundnessConfig.General
      else if (formulas forall (_.predicates.isEmpty))
        Theory.SatSoundnessConfig.Elementary
      else
        Theory.SatSoundnessConfig.Existential

    private lazy val theoriesAreSatComplete =
      theories.isEmpty || {
        val config = getSatSoundnessConfig
        (theories forall (_.isSoundForSat(theories, config)))
      }

    private lazy val allFunctionsArePartial =
      (formulas forall { f => f.predicates forall {
         p => (functionEncoder.predTranslation get p) match {
                 case Some(f) => f.partial
                 case None => true
               }
       }}) &&
      (theories forall { t => t.functions forall (_.partial) })

    lazy val soundForSat =
      !ignoredQuantifiers &&
      theoriesAreSatComplete &&
      (!matchedTotalFunctions || allFunctionsArePartial ||
       Param.GENERATE_TOTALITY_AXIOMS(settings)
       /*
        Enabling this last case gives a wrong result for
        testcases/onlyUnitResolution/functions5.pri
        with options -generateTriggers=complete -genTotalityAxioms
        Need a better criterion for when this trigger strategy
        is complete
       ||
       (Set(Param.TriggerGenerationOptions.Complete,
            Param.TriggerGenerationOptions.CompleteFrugal) contains
        Param.TRIGGER_GENERATION(settings))
        */
       )

    ////////////////////////////////////////////////////////////////////////////

    private val postprocessing =
      new Postprocessing(transSignature,
                         functionEncoder.predTranslation)

    def processModel(c : Conjunction) =
      postprocessing.processModel(c)
    def processConstraint(c : Conjunction) =
      postprocessing.processConstraint(c)
    def processInterpolant(c : Conjunction) =
      postprocessing.processInterpolant(c)

    def XtoIFormula(c : Conjunction,
                   onlyNonTheory : Boolean = false) = {
      val remaining = if (onlyNonTheory) filterNonTheoryParts(c) else c
      val remainingNoTypes = TypeTheory.filterTypeConstraints(remaining)
      val raw = Internal2InputAbsy(remainingNoTypes,
                                   functionEncoder.predTranslation)
      val simp = (new ArraySimplifier)(raw)
      implicit val context = new Theory.DefaultDecoderContext(c)
      IntToTermTranslator(simp)
    }

    ////////////////////////////////////////////////////////////////////////////

    def findModelTimeout : Either[Conjunction, Certificate] = {
      Console.withOut(Console.err) {
        println("Constructing satisfying assignment for the existential constants ...")
      }

      val formula = Conjunction.conj(formulas, order)
      val exConstraintFormula = 
        TypeTheory.addExConstraints(formula.negate,
                                    transSignature.existentialConstants,
                                    order)

      findCounterModelTimeout(List(exConstraintFormula.negate))
    }

    def findModel(f : Conjunction) : Conjunction = {
      val exConstraintFormula = 
        TypeTheory.addExConstraints(f,
                                    transSignature.existentialConstants,
                                    order)
      ModelSearchProver(exConstraintFormula.negate, f.order)
    }
  
    def findCounterModelTimeout : Either[Conjunction, Certificate] = {
      Console.withOut(Console.err) {
        println("Constructing countermodel ...")
      }
      findCounterModelTimeout(if (formulas exists (_.isTrue))
                                List(Conjunction.TRUE)
                              else
                                formulas)
    }
  
    def findCounterModelTimeout(f : Seq[Conjunction]) =
      Timeout.withChecker(stoppingCond) {
        ModelSearchProver(f, order, goalSettings, Param.COMPUTE_MODEL(settings))
      }

    def constructProofTree(name : String) : (ProofTree, Boolean) = {
      // explicitly quantify all universal variables
      
      val closedFor =
        Conjunction.quantify(Quantifier.ALL,
                             (order sort transSignature.nullaryFunctions).reverse,
                             Conjunction.disj(formulas, order), order)
  
      val closedExFor =
        TypeTheory.addExConstraints(closedFor,
                                    transSignature.existentialConstants,
                                    order)
      
      Console.withOut(Console.err) {
        println(name + " ...")
      }
      
      Timeout.withChecker(stoppingCond) {
        // TODO: can we sometimes use the QuantifierElimProver at this
        // point?

        val prover =
          new ExhaustiveProver(!Param.MOST_GENERAL_CONSTRAINT(settings) ||
                               Seqs.disjoint(transSignature.existentialConstants,
                                             formulaConstants),
                               goalSettings)
        val tree = prover(closedExFor, transSignature)
        val validConstraint =
          prover.isValidConstraint(tree.closingConstraint, transSignature)
        (tree, validConstraint)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor to check whether a formula is in the forall-exists fragment
   * (when proving that the formula is valid)
   */
  protected object AllExVisitor
            extends ap.parser.ContextAwareVisitor[Unit, Unit] {
    object NotInFragment extends Exception

    import ap.parser._

    def apply(t : IExpression) : Boolean = try {
      visit(t, Context(()))
      true
    } catch {
      case NotInFragment => false
    }

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case IQuantified(Quantifier.ALL, _)
        if ctxt.polarity >= 0 && (ctxt.binders contains Context.EX) =>
          throw NotInFragment
      case IQuantified(Quantifier.EX, _)
        if ctxt.polarity <= 0 && (ctxt.binders contains Context.EX) =>
          throw NotInFragment
      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression,
                  ctxt : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()    
  }

  //////////////////////////////////////////////////////////////////////////////

  protected lazy val posTranslation =
    new Translation(rawInputFormula, settings)

  protected lazy val negTranslation = {
    val order =
      rawSignature.order

    val booleanVars =
      for (p <- order sortPreds order.orderedPredicates; if p.arity == 0)
      yield p
    val booleanConsts =
      for (p <- booleanVars) yield new ConstantTerm (p.name)

    val subst =
      (for ((p, c) <- booleanVars.iterator zip booleanConsts.iterator)
       yield (p -> IExpression.eqZero(c))).toMap
    val substFor =
      UniformSubstVisitor(rawInputFormula, subst)

    val quantifiedConsts =
      (order sort (rawSignature.nullaryFunctions ++
                   rawSignature.universalConstants)).reverse ++ booleanConsts

    val quanFor =
      IExpression.quanConsts(Quantifier.ALL, quantifiedConsts, substFor)

    new Translation(!quanFor,
                    Param.CLAUSIFIER.set(settings,
                                         Param.ClausifierOptions.ExMaxiscope))
  }

  protected val usedTranslation : Translation

  //////////////////////////////////////////////////////////////////////////////

  def inputFormulas : List[INamedPart] =
    usedTranslation.inputFormulas
  def interpolantSpecs : List[IInterpolantSpec] =
    usedTranslation.preprocInterpolantSpecs
  def signature : Signature =
    usedTranslation.transSignature

  override def getFormulaParts : Map[PartName, Conjunction] =
    usedTranslation.getFormulaParts
  override def getAssumedFormulaParts(cert : Certificate) : Set[PartName] =
    usedTranslation.getAssumedFormulaParts(cert)
  override def getPredTranslation : Map[Predicate, IFunction] =
    usedTranslation.getPredTranslation

}
