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

import ap.theories.ADT.TermMeasure
import ap.theories.strings.StringTheoryBuilder
import ap.Signature.PredicateMatchConfig
import ap.proof.tree.{RandomDataSource, NonRandomDataSource}
import ap.terfor.conjunctions.{ReducerPluginFactory, IdentityReducerPlugin}

object Param {
  
  case object VERSION extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object LOGO extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }

  case object FULL_HELP extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  /**
   * Enable logging to stderr for specific aspects of the system.
   */
  case object LOG_LEVEL extends Param {
    type Value = Set[LOG_FLAG]
    val defau : Set[LOG_FLAG] = Set()
  }

  abstract class LOG_FLAG
  case object LOG_TASKS        extends LOG_FLAG
  case object LOG_SPLITS       extends LOG_FLAG
  case object LOG_BACKTRACKING extends LOG_FLAG
  case object LOG_STATS        extends LOG_FLAG

  case object QUIET extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  object InputFormat extends Enumeration {
    val Auto, Princess, SMTLIB, TPTP = Value
  }

  case object INPUT_FORMAT extends Param {
    type Value = InputFormat.Value
    val defau : InputFormat.Value = InputFormat.Auto
  }
  
  case object STDIN extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object INCREMENTAL extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object ASSERTIONS extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object PRINT_TREE extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object PRINT_SMT_FILE extends Param {
    type Value = String
    val defau : String = ""
  }
  
  case object PRINT_TPTP_FILE extends Param {
    type Value = String
    val defau : String = ""
  }
  
  case object PRINT_DOT_CERTIFICATE_FILE extends Param {
    type Value = String
    val defau : String = ""
  }
  
  case object PRINT_CERTIFICATE extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  object ConstraintSimplifierOptions extends Enumeration {
    val None, Fair, Lemmas = Value
  }
  case object SIMPLIFY_CONSTRAINTS extends Param {
    type Value = ConstraintSimplifierOptions.Value
    val defau : ConstraintSimplifierOptions.Value = ConstraintSimplifierOptions.Lemmas
  }
  
  case object TRACE_CONSTRAINT_SIMPLIFIER extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  /**
   * Represent numeric side conditions (inequalities) in quantified formulas
   * using the <code>StrengthenTree</code> constructor
   */
  case object STRENGTHEN_TREE_FOR_SIDE_CONDITIONS extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object MOST_GENERAL_CONSTRAINT extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  /** Turn ground constraints into disjunctive normal form */
  case object DNF_CONSTRAINTS extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }
  
  case object TIMEOUT extends Param {
    type Value = Int
    val defau : Int = Int.MaxValue
  }

  case object TIMEOUT_PER extends Param {
    type Value = Int
    val defau : Int = Int.MaxValue
  }

  /** Resolve negative predicate literals in clauses with positive facts */
  case object POS_UNIT_RESOLUTION extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }
  
  object ClausifierOptions extends Enumeration {
    val None, Simple, ExMaxiscope = Value
  }
  case object CLAUSIFIER extends Param {
    type Value = ClausifierOptions.Value
    val defau : ClausifierOptions.Value = ClausifierOptions.None
  }

  object TriggerGenerationOptions extends Enumeration {
    val None, Total, All,
        // Modes that generate triggers in such a way that a
        // complete FOL prover is obtained
        Complete, CompleteFrugal = Value
  }
  case object TRIGGER_GENERATION extends Param {
    type Value = TriggerGenerationOptions.Value
    val defau : TriggerGenerationOptions.Value = TriggerGenerationOptions.Total
  }

  case object GENERATE_TOTALITY_AXIOMS extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }

  object TriggerStrategyOptions extends Enumeration {
    val AllMinimal, AllMinimalAndEmpty,
        AllUni, AllMaximal,
        Maximal, MaximalOutermost = Value
  }
  case object TRIGGER_STRATEGY extends Param {
    type Value = TriggerStrategyOptions.Value
    val defau : TriggerStrategyOptions.Value = TriggerStrategyOptions.Maximal
  }

  case object TRIGGERS_IN_CONJECTURE extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }
  
  case object BOOLEAN_FUNCTIONS_AS_PREDICATES extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  /**
   * Use heuristics to distinguish between constructor and query
   * function symbols, and make the latter ones partial
   */
  case object MAKE_QUERIES_PARTIAL extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  /**
   * During pre-processing, inline equivalences of the form
   * <code>p <-> f</code>, for some Boolean variable p.
   */
  case object EQUIV_INLINING extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }

  case object REAL_RAT_SATURATION_ROUNDS extends Param {
    type Value = Int
    val defau : Int = 0
  }

  /** Portfolios optimised for particular domains */
  object PortfolioOptions extends Enumeration {
    val None, CASC, QF_LIA, BV = Value
  }

  case object PORTFOLIO extends Param {
    type Value = PortfolioOptions.Value
    val defau : PortfolioOptions.Value = PortfolioOptions.None
  }

  case object PORTFOLIO_THREAD_NUM extends Param {
    type Value = Int
    val defau : Int = 1
  }

  object NegSolvingOptions extends Enumeration {
    val Auto, Positive, Negative = Value
  }
  
  /** Options for solving problems in positive or negated version */
  case object NEG_SOLVING extends Param {
    type Value = NegSolvingOptions.Value
    val defau : NegSolvingOptions.Value = NegSolvingOptions.Auto
  }
  
  case object SYMBOL_WEIGHTS extends Param {
    type Value = ap.proof.goal.SymbolWeights
    val defau : ap.proof.goal.SymbolWeights = ap.proof.goal.SymbolWeights.DEFAULT
  }

  case object GARBAGE_COLLECTED_FUNCTIONS extends Param {
    type Value = Set[ap.terfor.preds.Predicate]
    val defau : Set[ap.terfor.preds.Predicate] = Set()
  }
  
  case object ABBREV_LABELS extends Param {
    type Value = Map[ap.terfor.preds.Predicate, ap.terfor.preds.Predicate]
    val defau : Map[ap.terfor.preds.Predicate, ap.terfor.preds.Predicate] =
      Map()
  }

  object FunctionGCOptions extends Enumeration {
    val None, Total, All = Value
  }
  case object FUNCTION_GC extends Param {
    type Value = FunctionGCOptions.Value
    val defau : FunctionGCOptions.Value = FunctionGCOptions.Total
  }
  
  case object TIGHT_FUNCTION_SCOPES extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }

  case object FUNCTIONAL_PREDICATES extends Param {
    type Value = Set[ap.terfor.preds.Predicate]
    val defau : Set[ap.terfor.preds.Predicate] = Set()
  }

  /**
   * Use the <code>FunctionalConsistency</code> dummy theory
   * to represent applications of functionality in proofs.
   */
  case object USE_FUNCTIONAL_CONSISTENCY_THEORY extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object STRING_THEORY_DESC extends Param {
    type Value = String
    val defau : String = "ap.theories.strings.SeqStringTheory"
  }

  case object SEQ_THEORY_DESC extends Param {
    type Value = String
    val defau : String = "ap.theories.sequences.ArraySeqTheory"
  }

  /**
   * Accept an extended set of escape sequences in strings:
   * \\, \x, \a, \b, \f, \n, \r, \t, \v. Without this option,
   * only the official SMT-LIB escapes are accepted.
   */
  case object STRING_ESCAPES extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object SINGLE_INSTANTIATION_PREDICATES extends Param {
    type Value = Set[ap.terfor.preds.Predicate]
    val defau : Set[ap.terfor.preds.Predicate] = Set()
  }

  /**
   * Even split propositional formulae that do not contain quantifiers or
   * eliminated constants
   */
  case object FULL_SPLITTING extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  /**
   * Even apply formulas that have been blocked, as last
   * steps in a proof. this can be necessary in order to
   * generate genuine models (<code>ModelSearchProver</code>)
   */
  case object APPLY_BLOCKED_TASKS extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object CONSTRAINT_SIMPLIFIER extends Param {
    type Value = ap.proof.ConstraintSimplifier
    val defau : ap.proof.ConstraintSimplifier =
      ap.proof.ConstraintSimplifier.FAIR_SIMPLIFIER
  }

  object MulProcedure extends Enumeration {
    val BitShift, Native = Value
  }

  case object MUL_PROCEDURE extends Param {
    type Value = MulProcedure.Value
    val defau : MulProcedure.Value = MulProcedure.Native
  }

  case object ADT_MEASURE extends Param {
    type Value = TermMeasure.Value
    val defau : TermMeasure.Value = TermMeasure.Size
  }

  object NonLinearSplitting extends Enumeration {
    val Spherical, Sign, SignMinimal = Value
  }

  case object NONLINEAR_SPLITTING extends Param {
    type Value = NonLinearSplitting.Value
    val defau : NonLinearSplitting.Value = NonLinearSplitting.Sign
  }

  case object PREDICATE_MATCH_CONFIG extends Param {
    type Value = PredicateMatchConfig
    val defau : PredicateMatchConfig = Map()
  }
  
  case object PROOF_CONSTRUCTION extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  /**
   * Globally, we can also choose to construct proofs depending on whether
   * interpolation specs were given (the default)
   */
  object ProofConstructionOptions extends Enumeration {
    val Never, Always, IfInterpolating = Value
  }
  case object PROOF_CONSTRUCTION_GLOBAL extends Param {
    type Value = ProofConstructionOptions.Value
    val defau : ProofConstructionOptions.Value =
      ProofConstructionOptions.IfInterpolating
  }

  case object COMPUTE_UNSAT_CORE extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object COMPUTE_MODEL extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  case object PROOF_SIMPLIFICATION extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }
  
  case object ELIMINATE_INTERPOLANT_QUANTIFIERS extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }

  /**
   * Ignore universal quantifiers in a problem that would require free
   * variables, by converting the quantifiers to existential ones.
   */
  case object IGNORE_QUANTIFIERS extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object REVERSE_FUNCTIONALITY_PROPAGATION extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object MATCHING_BASE_PRIORITY extends Param {
    type Value = Int
    val defau : Int = 500
  }

  case object THEORY_PLUGIN extends Param {
    type Value = Option[ap.proof.theoryPlugins.Plugin]
    val defau : Option[ap.proof.theoryPlugins.Plugin] = None
  }

  case object MODEL_GENERATION extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object RANDOM_DATA_SOURCE extends Param {
    type Value = RandomDataSource
    val defau : RandomDataSource = NonRandomDataSource
  }

  case object RANDOM_SEED extends Param {
    type Value = Option[Int]
    val defau : Option[Int] = Some(1234567)
  }

  case object REDUCER_SETTINGS extends Param {
    type Value = ReducerSettings
    val defau : ReducerSettings = ReducerSettings.DEFAULT
  }

  case object REDUCER_PLUGIN extends Param {
    type Value = ReducerPluginFactory
    val defau : ReducerPluginFactory = IdentityReducerPlugin.factory
  }
}

abstract class Param {
  
  type Value
  
  val defau : Value
  
  def apply[A <: Settings[A]](settings : Settings[A]) : Value =
    settings(this).asInstanceOf[Value]
  
  def set[A <: Settings[A]](settings : Settings[A], v : Value) : A =
    settings + (this, v)
    
}
