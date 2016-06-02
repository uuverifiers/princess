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

package ap.parameters;

import ap.Signature.PredicateMatchConfig

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
  
  case object MOST_GENERAL_CONSTRAINT extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  // turn ground constraints into disjunctive normal form
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

  // resolve negative predicate literals in clauses with positive facts
  case object POS_UNIT_RESOLUTION extends Param {
    type Value = Boolean
    val defau : Boolean = true
  }
  
  object ClausifierOptions extends Enumeration {
    val None, Simple = Value
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
  
  // Use heuristics to distinguish between constructor and query
  // function symbols, and make the latter ones partial
  case object MAKE_QUERIES_PARTIAL extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }

  case object REAL_RAT_SATURATION_ROUNDS extends Param {
    type Value = Int
    val defau : Int = 0
  }

  case object MULTI_STRATEGY extends Param {
    type Value = Boolean
    val defau : Boolean = false
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

  case object SINGLE_INSTANTIATION_PREDICATES extends Param {
    type Value = Set[ap.terfor.preds.Predicate]
    val defau : Set[ap.terfor.preds.Predicate] = Set()
  }

  // even split propositional formulae that do not contain quantifiers or
  // eliminated constants
  case object FULL_SPLITTING extends Param {
    type Value = Boolean
    val defau : Boolean = false
  }
  
  // even apply formulas that have been blocked, as last
  // steps in a proof. this can be necessary in order to
  // generate genuine models (<code>ModelSearchProver</code>)
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

  object NonLinearSplitting extends Enumeration {
    val Spherical, Sign = Value
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

  // globally, we can also choose to construct proofs depending on whether
  // interpolation specs were given (the default)
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
}

abstract class Param {
  
  type Value
  
  val defau : Value
  
  def apply[A <: Settings[A]](settings : Settings[A]) : Value =
    settings(this).asInstanceOf[Value]
  
  def set[A <: Settings[A]](settings : Settings[A], v : Value) : A =
    settings + (this, v)
    
}
