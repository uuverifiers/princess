/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parameters;

import ap.util.{Debug, Seqs, CmdlParser}

object Settings {
  
  private val AC = Debug.AC_PARAMETERS
  
}

object GlobalSettings {
  
  import CmdlParser._

  def fromArguments(args : Seq[String]) : (GlobalSettings, Seq[String]) =
    fromArguments(args, DEFAULT)
    
  def fromArguments(args : Seq[String],
                    initSettings : GlobalSettings) : (GlobalSettings, Seq[String]) = {
    var settings = initSettings
    val inputs = new scala.collection.mutable.ArrayBuffer[String]
    
    for (arg <- args)
      settings = arg match {
        case Opt("version", value) =>
         Param.VERSION.set(settings, value)
        case Opt("logo", value) =>
          Param.LOGO.set(settings, value)
        case Opt("fullHelp", value) =>
          Param.FULL_HELP.set(settings, value)
        case Opt("quiet", value) =>
          Param.QUIET.set(settings, value)
        case ValueOpt("logging", opts) =>
          Param.LOG_LEVEL.set(settings,
            ((opts split ",") map (logFlagFromString _)).toSet)
        case ValueOpt("inputFormat", "auto") =>
          Param.INPUT_FORMAT.set(settings, Param.InputFormat.Auto)
        case ValueOpt("inputFormat", "pri") =>
          Param.INPUT_FORMAT.set(settings, Param.InputFormat.Princess)
        case ValueOpt("inputFormat", "smtlib") =>
          Param.INPUT_FORMAT.set(settings, Param.InputFormat.SMTLIB)
        case ValueOpt("inputFormat", "tptp") =>
          Param.INPUT_FORMAT.set(settings, Param.InputFormat.TPTP)
        case Opt("stdin", value) =>
          Param.STDIN.set(settings, value)
        case Opt("incremental", value) => {
          val settings2 = Param.INCREMENTAL.set(settings, value)
          if (value)
            Param.GENERATE_TOTALITY_AXIOMS.set(settings2, false)
          else
            settings2
        }
        case Opt("printTree", value) =>
          Param.PRINT_TREE.set(settings, value)
        case ValueOpt("printSMT", value) =>
          Param.PRINT_SMT_FILE.set(settings, value)
        case ValueOpt("printTPTP", value) =>
          Param.PRINT_TPTP_FILE.set(settings, value)
        case Opt("printProof", value) =>
          Param.PRINT_CERTIFICATE.set(settings, value)
        case ValueOpt("printDOT", value) =>
          Param.PRINT_DOT_CERTIFICATE_FILE.set(settings, value)
        case Opt("assert", value) =>
          Param.ASSERTIONS.set(settings, value)
        case ValueOpt("simplifyConstraints", "none") =>
          Param.SIMPLIFY_CONSTRAINTS.set(settings,
                                         Param.ConstraintSimplifierOptions.None)
        case ValueOpt("simplifyConstraints", "fair") =>
          Param.SIMPLIFY_CONSTRAINTS.set(settings,
                                         Param.ConstraintSimplifierOptions.Fair)
        case ValueOpt("simplifyConstraints", "lemmas") =>
          Param.SIMPLIFY_CONSTRAINTS.set(settings,
                                         Param.ConstraintSimplifierOptions.Lemmas)
        case Opt("traceConstraintSimplifier", value) =>
          Param.TRACE_CONSTRAINT_SIMPLIFIER.set(settings, value)
        case Opt("useStrengthenTree", value) =>
          Param.STRENGTHEN_TREE_FOR_SIDE_CONDITIONS.set(settings, value)
        case Opt("mostGeneralConstraint", value) =>
          Param.MOST_GENERAL_CONSTRAINT.set(settings, value)
        case Opt("dnfConstraints", value) =>
          Param.DNF_CONSTRAINTS.set(settings, value)
        case ValueOpt("timeout", IntVal(value)) =>
          Param.TIMEOUT.set(settings, value)
        case ValueOpt("timeoutSec", IntVal(value)) =>
          Param.TIMEOUT.set(settings, value * 1000)
        case ValueOpt("timeoutPer", IntVal(value)) =>
          Param.TIMEOUT_PER.set(settings, value)
        case ValueOpt("counterTimeout", LongVal(value)) =>
          Param.COUNTER_TIMEOUT.set(settings, value)
        case Opt("posUnitResolution", value) =>
          Param.POS_UNIT_RESOLUTION.set(settings, value)
        case ValueOpt("clausifier", "none") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.None)
        case ValueOpt("clausifier", "simple") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.Simple)
        case Opt("equivInlining", value) =>
          Param.EQUIV_INLINING.set(settings, value)
        case ValueOpt("inlineSizeLimit", IntVal(value)) =>
          Param.INLINE_SIZE_LIMIT.set(settings, value)
        case ValueOpt("constructProofs", "never") =>
          Param.PROOF_CONSTRUCTION_GLOBAL.set(settings,
                                              Param.ProofConstructionOptions.Never)
        case ValueOpt("constructProofs", "always") =>
          Param.PROOF_CONSTRUCTION_GLOBAL.set(settings,
                                              Param.ProofConstructionOptions.Always)
        case ValueOpt("constructProofs", "ifInterpolating") =>
          Param.PROOF_CONSTRUCTION_GLOBAL.set(settings,
                                              Param.ProofConstructionOptions.IfInterpolating)
        case Opt("simplifyProofs", value) =>
          Param.PROOF_SIMPLIFICATION.set(settings, value)
        case Opt("unsatCore", value) =>
          Param.COMPUTE_UNSAT_CORE.set(settings, value)
        case Opt("model", value) =>
          Param.COMPUTE_MODEL.set(settings, value)
        case Opt("elimInterpolantQuants", value) =>
          Param.ELIMINATE_INTERPOLANT_QUANTIFIERS.set(settings, value)
        case Opt("ignoreQuantifiers", value) =>
          Param.IGNORE_QUANTIFIERS.set(settings, value)
        case ValueOpt("generateTriggers", "none") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.None)
        case ValueOpt("generateTriggers", "total") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.Total)
        case ValueOpt("generateTriggers", "all") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.All)
        case ValueOpt("generateTriggers", "complete") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.Complete)
        case ValueOpt("generateTriggers", "completeFrugal") =>
          Param.TRIGGER_GENERATION.set(settings,
                               Param.TriggerGenerationOptions.CompleteFrugal)
        case ValueOpt("functionGC", "none") =>
          Param.FUNCTION_GC.set(settings, Param.FunctionGCOptions.None)
        case ValueOpt("functionGC", "total") =>
          Param.FUNCTION_GC.set(settings, Param.FunctionGCOptions.Total)
        case ValueOpt("functionGC", "all") =>
          Param.FUNCTION_GC.set(settings, Param.FunctionGCOptions.All)
        case Opt("boolFunsAsPreds", value) =>
          Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(settings, value)
        case Opt("tightFunctionScopes", value) =>
          Param.TIGHT_FUNCTION_SCOPES.set(settings, value)
        case Opt("genTotalityAxioms", value) =>
          Param.GENERATE_TOTALITY_AXIOMS.set(settings, value)
        case ValueOpt("matchingBasePriority", IntVal(value)) =>
          Param.MATCHING_BASE_PRIORITY.set(settings, value)
        case Opt("reverseFunctionalityPropagation", value) =>
          Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(settings, value)
        case Opt("useFunctionalConsistencyTheory", value) =>
          Param.USE_FUNCTIONAL_CONSISTENCY_THEORY.set(settings, value)
        case ValueOpt("triggerStrategy", "allMinimal") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.AllMinimal)
        case ValueOpt("triggerStrategy", "allUni") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.AllUni)
        case ValueOpt("triggerStrategy", "allMinimalAndEmpty") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.AllMinimalAndEmpty)
        case ValueOpt("triggerStrategy", "allMaximal") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.AllMaximal)
        case ValueOpt("triggerStrategy", "maximal") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.Maximal)
        case ValueOpt("triggerStrategy", "maximalOutermost") =>
          Param.TRIGGER_STRATEGY.set(settings, Param.TriggerStrategyOptions.MaximalOutermost)
        case Opt("triggersInConjecture", value) =>
          Param.TRIGGERS_IN_CONJECTURE.set(settings, value)
        case ValueOpt("mulProcedure", "bitShift") =>
          Param.MUL_PROCEDURE.set(settings, Param.MulProcedure.BitShift)
        case ValueOpt("mulProcedure", "native") =>
          Param.MUL_PROCEDURE.set(settings, Param.MulProcedure.Native)
        case ValueOpt("mulSplitting", "sign") =>
          Param.NONLINEAR_SPLITTING.set(settings, Param.NonLinearSplitting.Sign)
        case ValueOpt("mulSplitting", "signMinimal") =>
          Param.NONLINEAR_SPLITTING.set(settings, Param.NonLinearSplitting.SignMinimal)
        case ValueOpt("adtMeasure", "size") =>
          Param.ADT_MEASURE.set(settings, ap.theories.ADT.TermMeasure.Size)
        case ValueOpt("adtMeasure", "relDepth") =>
          Param.ADT_MEASURE.set(settings, ap.theories.ADT.TermMeasure.RelDepth)
        case ValueOpt("realRatSaturationRounds", IntVal(value)) =>
          Param.REAL_RAT_SATURATION_ROUNDS.set(settings, value)
        case ValueOpt("stringSolver", value) =>
          Param.STRING_THEORY_DESC.set(settings, value)
        case ValueOpt("seqSolver", value) =>
          Param.SEQ_THEORY_DESC.set(settings, value)
        case Opt("stringEscapes", value) =>
          Param.STRING_ESCAPES.set(settings, value)
        case ValueOpt("randomSeed", "off") =>
          Param.RANDOM_SEED.set(settings, None)
        case ValueOpt("randomSeed", IntVal(value)) =>
          Param.RANDOM_SEED.set(settings, Some(value))
        case Opt("multiStrategy", value) =>
          Param.PORTFOLIO.set(settings, "casc")
        case ValueOpt("portfolio", portfolio) =>
          Param.PORTFOLIO.set(settings, portfolio)
        case Opt("threads", false) =>
          Param.PORTFOLIO_THREAD_NUM.set(settings, 1)
        case Opt("threads", true) =>
          Param.PORTFOLIO_THREAD_NUM.set(settings, 
            2 max (Runtime.getRuntime().availableProcessors - 1) min 16)
        case ValueOpt("threads", IntVal(num)) =>
          Param.PORTFOLIO_THREAD_NUM.set(settings, num)
        case ValueOpt("formulaSign", "positive") =>
          Param.NEG_SOLVING.set(settings, Param.NegSolvingOptions.Positive)
        case ValueOpt("formulaSign", "negative") =>
          Param.NEG_SOLVING.set(settings, Param.NegSolvingOptions.Negative)
        case ValueOpt("formulaSign", "auto") =>
          Param.NEG_SOLVING.set(settings, Param.NegSolvingOptions.Auto)
        case Opt(_, _) =>
          throw new UnknownArgumentException(arg)
        case _ => { inputs += arg; settings }
      }
    
    (settings, inputs)
  }

  def logFlagFromString(str : String) : Param.LOG_FLAG = str match {
    case "tasks"        => Param.LOG_TASKS
    case "splits"       => Param.LOG_SPLITS
    case "backtracking" => Param.LOG_BACKTRACKING
    case "stats"        => Param.LOG_STATS
    case "lemmas"       => Param.LOG_LEMMAS
    case "counters"     => Param.LOG_COUNTERS
    case str            => throw new UnknownArgumentException(str)
  }

  val allParams =
    List(Param.VERSION, Param.LOGO, Param.FULL_HELP,
         Param.QUIET, Param.LOG_LEVEL, Param.INPUT_FORMAT, Param.STDIN,
         Param.INCREMENTAL, Param.ASSERTIONS, Param.PRINT_TREE,
         Param.PRINT_SMT_FILE, Param.PRINT_TPTP_FILE,
         Param.PRINT_DOT_CERTIFICATE_FILE, Param.PRINT_CERTIFICATE,
         Param.SIMPLIFY_CONSTRAINTS, Param.TRACE_CONSTRAINT_SIMPLIFIER,
         Param.STRENGTHEN_TREE_FOR_SIDE_CONDITIONS,
         Param.MOST_GENERAL_CONSTRAINT, Param.DNF_CONSTRAINTS,
         Param.TIMEOUT, Param.TIMEOUT_PER, Param.COUNTER_TIMEOUT,
         Param.POS_UNIT_RESOLUTION, Param.CLAUSIFIER, Param.EQUIV_INLINING,
         Param.PROOF_CONSTRUCTION_GLOBAL, Param.COMPUTE_UNSAT_CORE,
         Param.COMPUTE_MODEL, Param.PROOF_SIMPLIFICATION,
         Param.TRIGGER_GENERATION, Param.FUNCTION_GC,
         Param.TIGHT_FUNCTION_SCOPES, Param.BOOLEAN_FUNCTIONS_AS_PREDICATES,
         Param.GENERATE_TOTALITY_AXIOMS,
         Param.ELIMINATE_INTERPOLANT_QUANTIFIERS, Param.IGNORE_QUANTIFIERS,
         Param.MATCHING_BASE_PRIORITY, Param.REVERSE_FUNCTIONALITY_PROPAGATION,
         Param.USE_FUNCTIONAL_CONSISTENCY_THEORY,
         Param.STRING_THEORY_DESC, Param.SEQ_THEORY_DESC,
         Param.STRING_ESCAPES, Param.TRIGGER_STRATEGY,
         Param.TRIGGERS_IN_CONJECTURE, Param.PORTFOLIO, Param.NEG_SOLVING,
         Param.NONLINEAR_SPLITTING, Param.MUL_PROCEDURE, Param.ADT_MEASURE,
         Param.REAL_RAT_SATURATION_ROUNDS, Param.RANDOM_SEED,
         Param.PORTFOLIO_THREAD_NUM, Param.INLINE_SIZE_LIMIT)

  val DEFAULT =
    new GlobalSettings (scala.collection.immutable.HashMap[Param, Any]())

}

object GoalSettings {

  val allParams = List(Param.POS_UNIT_RESOLUTION, Param.SYMBOL_WEIGHTS,
                       Param.GARBAGE_COLLECTED_FUNCTIONS,
                       Param.FUNCTIONAL_PREDICATES,
                       Param.SINGLE_INSTANTIATION_PREDICATES,
                       Param.FULL_SPLITTING, Param.APPLY_BLOCKED_TASKS,
                       Param.CONSTRAINT_SIMPLIFIER,
                       Param.STRENGTHEN_TREE_FOR_SIDE_CONDITIONS,
                       Param.PROOF_CONSTRUCTION, Param.MATCHING_BASE_PRIORITY,
                       Param.REVERSE_FUNCTIONALITY_PROPAGATION,
                       Param.USE_FUNCTIONAL_CONSISTENCY_THEORY,
                       Param.THEORY_PLUGIN, Param.PREDICATE_MATCH_CONFIG,
                       Param.NONLINEAR_SPLITTING, Param.ABBREV_LABELS,
                       Param.RANDOM_DATA_SOURCE, Param.REDUCER_SETTINGS,
                       Param.MODEL_GENERATION, Param.LOG_LEVEL)

  val DEFAULT =
    new GoalSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object ParserSettings {

  val allParams = List(Param.BOOLEAN_FUNCTIONS_AS_PREDICATES,
                       Param.TRIGGERS_IN_CONJECTURE,
                       Param.MAKE_QUERIES_PARTIAL,
                       Param.MUL_PROCEDURE, Param.ADT_MEASURE,
                       Param.REAL_RAT_SATURATION_ROUNDS,
                       Param.STRING_THEORY_DESC, Param.STRING_ESCAPES,
                       Param.SEQ_THEORY_DESC, Param.LOG_LEVEL,
                       Param.INLINE_SIZE_LIMIT)

  val DEFAULT =
    new ParserSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object PreprocessingSettings {

  val allParams = List(Param.CLAUSIFIER, Param.EQUIV_INLINING,
                       Param.TIGHT_FUNCTION_SCOPES, Param.TRIGGER_STRATEGY,
                       Param.TRIGGER_GENERATION,
                       Param.GENERATE_TOTALITY_AXIOMS, Param.LOG_LEVEL)

  val DEFAULT =
    new PreprocessingSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object ReducerSettings {

  val allParams = List(Param.FUNCTIONAL_PREDICATES, Param.REDUCER_PLUGIN,
                       Param.LOG_LEVEL)

  val DEFAULT =
    new ReducerSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

abstract class Settings[STT <: Settings[STT]]
                       (protected val paramMap : Map[Param, Any]) {

  // all parameters that are allowed for this kind of setting
  protected val allParams : List[Param]
  private lazy val allValues = for (p <- allParams) yield this(p)  
  
  protected def setParams(paramMap : Map[Param, Any]) : STT
  
  protected[parameters] def apply(p : Param) : Any = {
    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertPre(Settings.AC, allParams contains p)
    //-END-ASSERTION-/////////////////////////////////////////////////////////
    (paramMap get p) match {
      case Some(value : Any) => {
        //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
        Debug.assertPost(Settings.AC, value.isInstanceOf[p.Value])
        //-END-ASSERTION-/////////////////////////////////////////////////////////
        value
      }
      case None => p.defau
    }
  }
  
  protected[parameters] def +(paramPair : (Param, Any)) : STT = {
    val (p, value) = paramPair
    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertPre(Settings.AC, (allParams contains p) &&
                                 value.isInstanceOf[p.Value])
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    setParams(paramMap + paramPair)
  }
  
  override def equals(that : Any) : Boolean = that match {
    case that : Settings[STT] => this.allValues sameElements that.allValues
    case _ => false
  }

  private lazy val hashCodeVal = Seqs.computeHashCode(this.allValues, 18732, 11)

  override def hashCode = hashCodeVal

  override def toString : String = "Settings(" + paramMap + ")"

  protected def subSettings[A <: Settings[A]]
                         (params : Seq[Param], init : A) : A = {
    var res = init
    
    for ((p, v) <- paramMap) {
      if (params contains p)
        res = res + (p, v)
    }
    
    res
  }

  def toGoalSettings : GoalSettings =
    subSettings(GoalSettings.allParams, GoalSettings.DEFAULT)
    
  def toParserSettings : ParserSettings =
    subSettings(ParserSettings.allParams, ParserSettings.DEFAULT)
    
  def toPreprocessingSettings : PreprocessingSettings =
    subSettings(PreprocessingSettings.allParams, PreprocessingSettings.DEFAULT)

  def toReducerSettings : ReducerSettings =
    subSettings(ReducerSettings.allParams, ReducerSettings.DEFAULT)
}

class GlobalSettings(_paramMap : Map[Param, Any])
      extends Settings[GlobalSettings](_paramMap) {
  protected val allParams = GlobalSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new GlobalSettings(paramMap)
}

class GoalSettings(_paramMap : Map[Param, Any])
      extends Settings[GoalSettings](_paramMap) {
  protected val allParams = GoalSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new GoalSettings(paramMap)
}

class ParserSettings(_paramMap : Map[Param, Any])
      extends Settings[ParserSettings](_paramMap) {
  protected val allParams = ParserSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new ParserSettings(paramMap)
}

class PreprocessingSettings(_paramMap : Map[Param, Any])
      extends Settings[PreprocessingSettings](_paramMap) {
  protected val allParams = PreprocessingSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new PreprocessingSettings(paramMap)
}

class ReducerSettings(_paramMap : Map[Param, Any])
      extends Settings[ReducerSettings](_paramMap) {
  protected val allParams = ReducerSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new ReducerSettings(paramMap)
}
