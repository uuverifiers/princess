/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

/**
 * Theory for performing bounded modulo-arithmetic (arithmetic modulo some
 * number N). This in particular includes bit-vector/machine arithmetic.
 *
 * Class under construction ...
 */
object ModuloArithmetic extends Theory {

  override def toString = "ModuloArithmetic"

  /**
   * Modulo and bit-vector operations.
   * See http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
   * for an explanation of the operations
   */

  // Arguments: N, any number
  // Result:    number mod N
  val mod_cast          = new IFunction("mod_cast",        2, true, false)

  // Arguments: N1, N2, number mod N1, number mod N2
  // Result:    number mod (N1 * N2)
  val mod_concat        = new IFunction("mod_concat",      4, true, false)
  
  // Arguments: N1, N2, N3, number mod (N1 * N2 * N3)
  // Result:    number mod N2
  val mod_extract       = new IFunction("mod_extract",     4, true, false)

  // Arguments: N, number mod N
  // Result:    number mod N
  val mod_not           = new IFunction("mod_not",         2, true, false)
  val mod_neg           = new IFunction("mod_neg",         2, true, false)

  // Arguments: N, number mod N, number mod N
  // Result:    number mod N
  val mod_and           = new IFunction("mod_and",         3, true, false)
  val mod_or            = new IFunction("mod_or",          3, true, false)
  val mod_add           = new IFunction("mod_add",         3, true, false)
  val mod_sub           = new IFunction("mod_sub",         3, true, false)
  val mod_mul           = new IFunction("mod_mul",         3, true, false)
  val mod_udiv          = new IFunction("mod_udiv",        3, true, false)
  val mod_sdiv          = new IFunction("mod_sdiv",        3, true, false)
  val mod_urem          = new IFunction("mod_urem",        3, true, false)
  val mod_srem          = new IFunction("mod_srem",        3, true, false)
  val mod_smod          = new IFunction("mod_smod",        3, true, false)
  val mod_shl           = new IFunction("mod_shl",         3, true, false)
  val mod_lshr          = new IFunction("mod_lshr",        3, true, false)
  val mod_ashr          = new IFunction("mod_ashr",        3, true, false)

  val mod_xor           = new IFunction("mod_xor",         3, true, false)
  val mod_xnor          = new IFunction("mod_xnor",        3, true, false)

  // Arguments: N, number mod N, number mod N
  // Result:    number mod 2
  val mod_comp          = new IFunction("mod_comp",        3, true, false)

  // Arguments: N, number mod N, number mod N
  val mod_ult           = new Predicate("mod_ult",         3)
  val mod_ule           = new Predicate("mod_ule",         3)
  val mod_slt           = new Predicate("mod_slt",         3)
  val mod_sle           = new Predicate("mod_sle",         3)

  //////////////////////////////////////////////////////////////////////////////

  val functions = List(
    mod_cast,
    mod_concat,
    mod_extract,
    mod_not,
    mod_neg,
    mod_and,
    mod_or,
    mod_add,
    mod_sub,
    mod_mul,
    mod_udiv,
    mod_sdiv,
    mod_urem,
    mod_srem,
    mod_smod,
    mod_shl,
    mod_lshr,
    mod_ashr,
    mod_xor,
    mod_xnor,
    mod_comp
  )

  val otherPreds = List(mod_ult, mod_ule, mod_slt, mod_sle)

  val (functionalPredSeq, axioms, preOrder, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  val functionPredicateMapping = functions zip functionalPredSeq
  val functionalPredicates = functionalPredSeq.toSet

  val order = preOrder extendPred otherPreds

  val predicates = otherPreds ++ functionalPredSeq
  val totalityAxioms = Conjunction.TRUE

  def plugin = None
  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = functions.toSet

  TheoryRegistry register this

}