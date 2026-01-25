/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2026 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.util.{Debug, Timeout, Seqs, OpCounters}

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

  private val AxiomParts = Set(PartName.FUNCTION_AXIOMS, PartName.THEORY_AXIOMS)

  //////////////////////////////////////////////////////////////////////////////

  def timeoutFromSettings(settings : GlobalSettings) : TimeoutCondition = {
    var res : TimeoutCondition = NoTimeoutCondition

    Param.TIMEOUT(settings) match {
      case Int.MaxValue => // nothing
      case timeout      => res = res | MsTimeoutCondition(timeout)
    }

    Param.COUNTER_TIMEOUT(settings) match {
      case Long.MaxValue => // nothing
      case timeout       => res = res | CounterTimeoutCondition(timeout)
    }

    res
  }

  /**
   * A simple representation of different timeout conditions.
   */
  abstract sealed class TimeoutCondition {
    def |(that : TimeoutCondition) : TimeoutCondition =
      if (this == NoTimeoutCondition)
        that
      else if (that == NoTimeoutCondition)
        this
      else
        OrTimeoutCondition(this, that)
  }

  case object NoTimeoutCondition                        extends TimeoutCondition

  /**
   * Wall-clock timeouts in milliseconds.
   */
  case class  MsTimeoutCondition     (limit : Long)     extends TimeoutCondition

  /**
   * Timeouts in terms of counter values, as defined by
   * <code>AbstractFileProver.counterTimeApproximation</code>
   */
  case class  CounterTimeoutCondition(limit : Long)     extends TimeoutCondition

  /**
   * Disjunction of two timeout conditions.
   */
  case class  OrTimeoutCondition(a : TimeoutCondition,
                                 b : TimeoutCondition)  extends TimeoutCondition

  /**
   * Check whether a timeout occurred. The second argument provides the
   * wall-clock start time.
   */
  def evalTimeoutCondition(cond : TimeoutCondition,
                           startTime : Long) : Boolean = cond match {
    case NoTimeoutCondition =>
      false
    case MsTimeoutCondition(limit) =>
      System.currentTimeMillis - startTime > limit
    case CounterTimeoutCondition(limit) =>
      counterTimeApproximation > limit
    case OrTimeoutCondition(a, b) =>
      evalTimeoutCondition(a, startTime) || evalTimeoutCondition(b, startTime)
  }

  def counterTimeApproximation : Long =
    (0.019 * OpCounters(OpCounters.TaskApplications) +
     1.120 * OpCounters(OpCounters.Backtrackings1) +
     0.007 * OpCounters(OpCounters.Reductions) +
     -0.124 * OpCounters(OpCounters.Backtrackings3) +
     0.167 * OpCounters(OpCounters.Splits3) +
     1.449 * OpCounters(OpCounters.Splits1) +
     0.038 * OpCounters(OpCounters.Backtrackings2) +
     4.515 * OpCounters(OpCounters.Splits2)).toLong

  def simpleCounterTimeApproximation : Long =
    OpCounters(OpCounters.TaskApplications)

}

abstract class AbstractFileProver(reader  : java.io.Reader,
                                  output  : Boolean,
                                  timeout : AbstractFileProver.TimeoutCondition,
                                  userDefStoppingCond : => Boolean,
                                  settings : GlobalSettings) extends Prover {

  import AbstractFileProver._

  private val startTime = System.currentTimeMillis

  private var counterPrintNum : Int =
    if (Param.LOG_LEVEL(settings) contains Param.LOG_COUNTERS_CONT)
      0
    else
      -1

  private val stoppingCond = () => {
    if (evalTimeoutCondition(timeout, startTime) || userDefStoppingCond)
      Timeout.raise
    if (counterPrintNum >= 0) {
      val time = System.currentTimeMillis
      if (time - startTime >= 500*(counterPrintNum + 1)) {
        Console.withOut(Console.err) {
          ap.util.OpCounters.printCounters
        }
        counterPrintNum = counterPrintNum + 1
      }
    }
  }

  protected def println(obj : Any) : Unit =
    println("" + obj)

  protected def println(str : => String) : Unit =
    (if (output) Predef.println(str))
  
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
  protected class Translation(preFormula   : IFormula,
                              preSignature : Signature,
                              settings     : GlobalSettings) {
    val (inputFormulas, preprocInterpolantSpecs, transSignature,
         gcedFunctions, functionEncoder, incompletePreproc) = {
      var incompletePreproc = false
  
      val preprocSettings = settings.toPreprocessingSettings
  
      Console.withOut(Console.err) {
        println("Preprocessing ...")
      }
      
      val genTotality =
        Param.GENERATE_TOTALITY_AXIOMS(settings) &&
        !IsUniversalFormulaVisitor(preFormula)
  
      val functionEnc =
        new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings), genTotality)
      for (t <- preSignature.theories)
        functionEnc addTheory t
  
      val ((inputFormulas, interpolantS, sig), incomp) = Incompleteness.track {
        Timeout.withChecker(stoppingCond) {
          val preFormula2 =
            if (constructProofs) {
              preFormula
            } else {
              // we keep part names that identify TPTP conjectures;
              // otherwise we won't be able to distinguish between
              // results Theorem/Unsatisfiable/etc. later.
              val elim =
                new PredPartNameEliminator(
                  name => TPTPTParser.ConjecturePartName.unapply(name).isEmpty)
              elim(preFormula)
            }
          Preprocessing(preFormula2, rawInterpolantSpecs,
                        preSignature, preprocSettings, functionEnc)
        }
      }

      if (incomp)
        incompletePreproc = true
      
      val sig2 =
        if (sig.isSorted)
          sig.addTheories(List(ap.types.TypeTheory), true)
        else
          sig
  
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
           rs, SeqReducerPluginFactory(for (t <- theories)
                                       yield t.reducerPlugin))
      rs
    }
  
    ////////////////////////////////////////////////////////////////////////////

    val (namedParts, formulas, matchedTotalFunctions, ignoredQuantifiers2) = {
      var ignoredQuantifiers = false
  
      val reducer =
        ReduceWithConjunction(Conjunction.TRUE, order, reducerSettings)
      val allPartNames =
        (PartName.predefNames ++
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
  
      // input: the conjecture to be proven
      // axiom: function axioms, added by the function encoder

      val (axioms, inputs) =
        inputFormulas partition {
          case INamedPart(n, _) => AxiomParts contains n
        }

      if (constructProofs) {

        // keep the different formula parts separate

        val Seq(axiomF, inputF) =
          for (fors <- Seq(axioms, inputs)) yield {
            (for (INamedPart(n, f) <- fors.iterator)
             yield (n -> reducer(Conjunction.conj(InputAbsy2Internal(f, order),
                                                  order)))).toMap
          }

        val matchedTotal = checkMatchedTotalFunctions(inputF map (_._2))

        val axiomF2 =
          axiomF mapValues { c => {
            Theory.preprocess(c, transSignature.theories, transSignature)
          }}

        val inputF2 =
          inputF mapValues { c => {
            val (redC, incomp) = Incompleteness.track {
              Theory.preprocess(c, transSignature.theories, transSignature)
            }
  
            if (incomp)
              ignoredQuantifiers = true

            redC
          }}
  
        val namedParts = (axiomF2 ++ inputF2) mapValues (convertQuantifiers _)

        val namedParts2 =
          if (theoryAxioms.isFalse)
            namedParts
          else
            namedParts + (PartName.THEORY_AXIOMS -> theoryAxioms)

        (namedParts2,
         for (n <- allPartNames; f <- namedParts2 get n) yield f,
         matchedTotal,
         ignoredQuantifiers)
         
      } else {

        // merge everything into one formula; we keep the axioms
        // separate, though, because we have to check for quantifier
        // occurrences in the non-axiom formulas.

        val Seq(axiomF, inputF) =
          for (fors <- Seq(axioms, inputs)) yield {
            reducer(
              Conjunction.conj(
                InputAbsy2Internal(
                  IExpression.or(for (f <- fors.iterator)
                                 yield (IExpression removePartName f)), order),
                order))
          }

        val matchedTotal =
          checkMatchedTotalFunctions(List(inputF))

        val allInputs =
          Conjunction.disjFor(List(axiomF, inputF), order)

        val (inputRed, incomp) = Incompleteness.track {
          convertQuantifiers(Theory.preprocess(allInputs,
                                               transSignature.theories,
                                               transSignature))
        }
  
        if (incomp)
          ignoredQuantifiers = true
  
        val f =
          Conjunction.disj(List(theoryAxioms, inputRed), order)

        (Map(PartName.NO_NAME -> f), List(f), matchedTotal, ignoredQuantifiers)
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
                   case Some(f) =>
                     // as a convention, all theory functions are considered
                     // to be total
                     !f.partial || TheoryRegistry.lookupSymbol(f).isDefined
                   case None =>
                     false
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

    def getInputFormulaParts : Map[PartName, IFormula] =
      (for (INamedPart(n, f) <- inputFormulas) yield (n -> f)).toMap

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
      if (!canUseModelSearchProver || matchedTotalFunctions)
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

  private def catchTranslationTimeout(comp : => Translation) : Translation =
    Timeout.catchTimeout[Translation] {
      comp
    } {
      case _ => null
    }

  protected lazy val posTranslation =
    catchTranslationTimeout(
      new Translation(rawInputFormula, rawSignature, settings))

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

    val negSignature =
      if (Param.MOST_GENERAL_CONSTRAINT(settings))
        rawSignature
      else
        // we can turn the the existential constants into nullary functions
        Signature(Set(), Set(), rawSignature.existentialConstants,
                  rawSignature.predicateMatchConfig,
                  rawSignature.order,
                  rawSignature.theories)

    catchTranslationTimeout(
      new Translation(!quanFor,
                      negSignature,
                      Param.CLAUSIFIER.set(settings,
                                           Param.ClausifierOptions.ExMaxiscope))
    )
  }

  protected val usedTranslation : Translation

  //////////////////////////////////////////////////////////////////////////////

  def inputFormulas : List[INamedPart] =
    usedTranslation.inputFormulas
  def interpolantSpecs : List[IInterpolantSpec] =
    usedTranslation.preprocInterpolantSpecs
  def signature : Signature =
    usedTranslation.transSignature

  override def getInputFormulaParts : Map[PartName, IFormula] =
    usedTranslation.getInputFormulaParts
  override def getFormulaParts : Map[PartName, Conjunction] =
    usedTranslation.getFormulaParts
  override def getAssumedFormulaParts(cert : Certificate) : Set[PartName] =
    usedTranslation.getAssumedFormulaParts(cert)
  override def getPredTranslation : Map[Predicate, IFunction] =
    usedTranslation.getPredTranslation

}
