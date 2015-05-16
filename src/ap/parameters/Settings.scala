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
        case Opt("quiet", value) =>
          Param.QUIET.set(settings, value)
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
        case Opt("mostGeneralConstraint", value) =>
          Param.MOST_GENERAL_CONSTRAINT.set(settings, value)
        case Opt("dnfConstraints", value) =>
          Param.DNF_CONSTRAINTS.set(settings, value)
        case ValueOpt("timeout", IntVal(value)) =>
          Param.TIMEOUT.set(settings, value)
        case ValueOpt("timeoutPer", IntVal(value)) =>
          Param.TIMEOUT_PER.set(settings, value)
        case Opt("posUnitResolution", value) =>
          Param.POS_UNIT_RESOLUTION.set(settings, value)
        case ValueOpt("clausifier", "none") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.None)
        case ValueOpt("clausifier", "simple") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.Simple)
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
        case ValueOpt("realRatSaturationRounds", IntVal(value)) =>
          Param.REAL_RAT_SATURATION_ROUNDS.set(settings, value)
        case Opt("multiStrategy", value) =>
          Param.MULTI_STRATEGY.set(settings, value)
        case Opt(_, _) =>
          throw new UnknownArgumentException(arg)
        case _ => { inputs += arg; settings }
      }
    
    (settings, inputs)
  }
  
  val allParams =
    List(Param.VERSION, Param.LOGO, Param.QUIET, Param.INPUT_FORMAT, Param.STDIN,
         Param.INCREMENTAL, Param.ASSERTIONS, Param.PRINT_TREE,
         Param.PRINT_SMT_FILE, Param.PRINT_TPTP_FILE,
         Param.PRINT_DOT_CERTIFICATE_FILE,
         Param.SIMPLIFY_CONSTRAINTS, Param.TRACE_CONSTRAINT_SIMPLIFIER,
         Param.MOST_GENERAL_CONSTRAINT, Param.DNF_CONSTRAINTS,
         Param.TIMEOUT, Param.TIMEOUT_PER,
         Param.POS_UNIT_RESOLUTION, Param.CLAUSIFIER,
         Param.PROOF_CONSTRUCTION_GLOBAL, Param.PROOF_SIMPLIFICATION,
         Param.TRIGGER_GENERATION, Param.FUNCTION_GC,
         Param.TIGHT_FUNCTION_SCOPES, Param.BOOLEAN_FUNCTIONS_AS_PREDICATES,
         Param.GENERATE_TOTALITY_AXIOMS,
         Param.ELIMINATE_INTERPOLANT_QUANTIFIERS, Param.IGNORE_QUANTIFIERS,
         Param.MATCHING_BASE_PRIORITY, Param.REVERSE_FUNCTIONALITY_PROPAGATION,
         Param.TRIGGER_STRATEGY, Param.TRIGGERS_IN_CONJECTURE,
         Param.MULTI_STRATEGY,
         Param.MUL_PROCEDURE, Param.REAL_RAT_SATURATION_ROUNDS)

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
                       Param.PROOF_CONSTRUCTION, Param.MATCHING_BASE_PRIORITY,
                       Param.REVERSE_FUNCTIONALITY_PROPAGATION,
                       Param.THEORY_PLUGIN, Param.PREDICATE_MATCH_CONFIG,
                       Param.NONLINEAR_SPLITTING)

  val DEFAULT =
    new GoalSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object ParserSettings {

  val allParams = List(Param.BOOLEAN_FUNCTIONS_AS_PREDICATES,
                       Param.TRIGGERS_IN_CONJECTURE,
                       Param.MAKE_QUERIES_PARTIAL,
                       Param.MUL_PROCEDURE,
                       Param.REAL_RAT_SATURATION_ROUNDS)

  val DEFAULT =
    new ParserSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object PreprocessingSettings {

  val allParams = List(Param.CLAUSIFIER,
                       Param.TIGHT_FUNCTION_SCOPES, Param.TRIGGER_STRATEGY,
                       Param.TRIGGER_GENERATION,
                       Param.GENERATE_TOTALITY_AXIOMS)

  val DEFAULT =
    new PreprocessingSettings (scala.collection.immutable.HashMap[Param, Any]())
  
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
}

class GlobalSettings(_paramMap : Map[Param, Any])
      extends Settings[GlobalSettings](_paramMap) {
  protected val allParams = GlobalSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new GlobalSettings(paramMap)
    
  private def subSettings[A <: Settings[A]]
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
