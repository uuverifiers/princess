/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.conjunctions.Conjunction

/**
 * A dummy theory that represents the functional consistency
 * axioms for functional predicates.
 */
object FunctionalConsistency extends Theory {

  val axioms: ap.terfor.Formula = Conjunction.TRUE
  val functionPredicateMapping: Seq[(ap.parser.IFunction, ap.parser.IExpression.Predicate)] = List()
  val functionalPredicates: Set[ap.parser.IExpression.Predicate] = Set()
  val functions: Seq[ap.parser.IFunction] = List()
  def plugin: Option[ap.proof.theoryPlugins.Plugin] = None
  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val predicates: Seq[ap.parser.IExpression.Predicate] = List()
  val totalityAxioms: ap.terfor.Formula = Conjunction.TRUE
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = "FunctionalConsistency"

}