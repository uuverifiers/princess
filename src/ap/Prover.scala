/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.proof.tree.ProofTree
import ap.proof.certificates.Certificate
import ap.parser.IFormula

object Prover {
  
  abstract sealed class Result
  
  abstract sealed class ProofResult extends Result
  case class Proof(tree : ProofTree) extends ProofResult
  case class ProofWithModel(tree : ProofTree, model : IFormula) extends ProofResult
  case class NoProof(unsatisfiableTree : ProofTree) extends ProofResult
  case class Invalid(unsatisfiableTree : ProofTree) extends ProofResult
  case class TimeoutProof(unfinishedTree : ProofTree) extends ProofResult

  // "model" means that the implicitly existentially quantified constants can be
  // instantiated so that the formula evaluates to true
  abstract sealed class ModelResult extends Result
  case class Model(model : IFormula) extends ModelResult
  case object NoModel extends ModelResult
  case object TimeoutModel extends ModelResult

  // "countermodel" means that the implicitly universally quantified constants
  // can be instantiated so that the formula evaluates to false
  abstract sealed class CounterModelResult extends Result
  case class CounterModel(counterModel : IFormula) extends CounterModelResult
  case class MaybeCounterModel(counterModel : IFormula) extends CounterModelResult
  case object NoCounterModel extends CounterModelResult
  case class NoCounterModelCert(certificate : Certificate) extends CounterModelResult
  case class NoCounterModelCertInter(certificate : Certificate,
                                     interpolants : Seq[IFormula])
             extends CounterModelResult
  case object TimeoutCounterModel extends CounterModelResult

}

/**
 * Trait characterising provers, which receive some problem (e.g., from a file)
 * and try to construct a proof, a countermodel, or interpolants
 */
trait Prover {

  val result : Prover.Result

}