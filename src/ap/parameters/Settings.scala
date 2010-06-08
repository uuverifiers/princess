/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
        case Opt("logo", value) =>
          Param.LOGO.set(settings, value)
        case Opt("printTree", value) =>
          Param.PRINT_TREE.set(settings, value)
        case ValueOpt("printSMT", value) =>
          Param.PRINT_SMT_FILE.set(settings, value)
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
        case Opt("posUnitResolution", value) =>
          Param.POS_UNIT_RESOLUTION.set(settings, value)
        case ValueOpt("clausifier", "none") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.None)
        case ValueOpt("clausifier", "simple") =>
          Param.CLAUSIFIER.set(settings, Param.ClausifierOptions.Simple)
        case Opt("constructProofs", value) =>
          Param.PROOF_CONSTRUCTION.set(settings, value)
        case ValueOpt("generateTriggers", "none") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.None)
        case ValueOpt("generateTriggers", "total") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.Total)
        case ValueOpt("generateTriggers", "all") =>
          Param.TRIGGER_GENERATION.set(settings,
                                       Param.TriggerGenerationOptions.All)
        case Opt(_, _) =>
          throw new UnknownArgumentException(arg)
        case _ => { inputs += arg; settings }
      }
    
    (settings, inputs)
  }
  
  val allParams =
    List(Param.LOGO, Param.ASSERTIONS, Param.PRINT_TREE, Param.PRINT_SMT_FILE,
         Param.SIMPLIFY_CONSTRAINTS, Param.TRACE_CONSTRAINT_SIMPLIFIER,
         Param.MOST_GENERAL_CONSTRAINT, Param.DNF_CONSTRAINTS,
         Param.TIMEOUT, Param.POS_UNIT_RESOLUTION, Param.CLAUSIFIER,
         Param.PROOF_CONSTRUCTION, Param.TRIGGER_GENERATION)

  val DEFAULT =
    new GlobalSettings (scala.collection.immutable.HashMap[Param, Any]())

}

object GoalSettings {

  val allParams = List(Param.POS_UNIT_RESOLUTION, Param.SYMBOL_WEIGHTS,
                       Param.FULL_SPLITTING, Param.CONSTRAINT_SIMPLIFIER,
                       Param.PROOF_CONSTRUCTION)

  val DEFAULT =
    new GoalSettings (scala.collection.immutable.HashMap[Param, Any]())
  
}

object PreprocessingSettings {

  val allParams = List(Param.CLAUSIFIER,
                       Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS)

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
}

class GlobalSettings(_paramMap : Map[Param, Any])
      extends Settings[GlobalSettings](_paramMap) {
  protected val allParams = GlobalSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new GlobalSettings(paramMap)
    
  def toGoalSettings : GoalSettings = {
    var res = GoalSettings.DEFAULT
    
    for ((p, v) <- paramMap) {
      if (GoalSettings.allParams contains p)
        res = res + (p, v)
    }
    
    res
  }
    
  def toPreprocessingSettings : PreprocessingSettings = {
    var res = PreprocessingSettings.DEFAULT
    
    for ((p, v) <- paramMap) {
      if (PreprocessingSettings.allParams contains p)
        res = res + (p, v)
    }
    
    res
  }
}

class GoalSettings(_paramMap : Map[Param, Any])
      extends Settings[GoalSettings](_paramMap) {
  protected val allParams = GoalSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new GoalSettings(paramMap)
}

class PreprocessingSettings(_paramMap : Map[Param, Any])
      extends Settings[PreprocessingSettings](_paramMap) {
  protected val allParams = PreprocessingSettings.allParams
  
  protected def setParams(paramMap : Map[Param, Any]) =
    new PreprocessingSettings(paramMap)
}
