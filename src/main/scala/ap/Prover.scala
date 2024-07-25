/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction
import ap.proof.tree.ProofTree
import ap.proof.certificates.Certificate
import ap.parser.{IFormula, IFunction, PartName}

object Prover {
  
  abstract sealed class Result
  
  //////////////////////////////////////////////////////////////////////////////
  // "proof" means a proof tree with satisfiable constraint has been found

  abstract sealed class ProofResult extends Result

  case class  Proof(tree : ProofTree, constraint : IFormula)
              extends ProofResult

  case class  ProofWithModel(tree : ProofTree,
                             constraint : IFormula,
                             model : IFormula)
              extends ProofResult

  case class  NoProof(unsatisfiableTree : ProofTree)
              extends ProofResult

  case class  Invalid(unsatisfiableTree : ProofTree)
              extends ProofResult

  case class  TimeoutProof(unfinishedTree : ProofTree)
              extends ProofResult

  //////////////////////////////////////////////////////////////////////////////
  // "model" means that the implicitly existentially quantified constants can be
  // instantiated so that the formula evaluates to true

  abstract sealed class ModelResult extends Result

  case class  Model(model : Option[IFormula])
              extends ModelResult

  case class  AllModels(constraint : IFormula, model : Option[IFormula])
              extends ModelResult

  case object NoModel
              extends ModelResult

  case object TimeoutModel
              extends ModelResult

  //////////////////////////////////////////////////////////////////////////////
  // "countermodel" means that the implicitly universally quantified constants
  // can be instantiated so that the formula evaluates to false

  abstract sealed class CounterModelResult extends Result

  case class  CounterModel(counterModel : Option[IFormula])
              extends CounterModelResult

  case class  MaybeCounterModel(counterModel : Option[IFormula])
              extends CounterModelResult

  case object NoCounterModel extends CounterModelResult

  case class  NoCounterModelCert(certificate : Certificate)
              extends CounterModelResult

  case class  NoCounterModelCertInter(certificate : Certificate,
                                     interpolants : Seq[IFormula])
              extends CounterModelResult

  case object TimeoutCounterModel
              extends CounterModelResult

  //////////////////////////////////////////////////////////////////////////////
  // Extractors to more easily interpret the results

  object ValidResult {
    def unapply(res : Result) : Boolean = res match {
      case Proof(_, _)                   => true
      case ProofWithModel(_, _, _)       => true
      case Model(_)                      => true
      case AllModels(_, _)               => true
      case NoCounterModel                => true
      case NoCounterModelCert(_)         => true
      case NoCounterModelCertInter(_, _) => true
      case _                             => false
    }
  }

  object InvalidResult {
    def unapply(res : Result) : Boolean = res match {
      case Invalid(_)                    => true
      case NoModel                       => true
      case CounterModel(_)               => true
      case _                             => false
    }
  }

  object InconclusiveResult {
    def unapply(res : Result) : Boolean = res match {
      case NoProof(_)                    => true
      case MaybeCounterModel(_)          => true
      case _                             => false
    }
  }

  object TimeoutResult {
    def unapply(res : Result) : Boolean = res match {
      case TimeoutProof(_)               => true
      case TimeoutModel                  => true
      case TimeoutCounterModel           => true
      case _                             => false
    }
  }

}

/**
 * Trait characterising provers, which receive some problem (e.g., from a file)
 * and try to construct a proof, a countermodel, or interpolants
 */
trait Prover {

  val result : Prover.Result

  def getInputFormulaParts : Map[PartName, IFormula] =
    throw new UnsupportedOperationException

  def getFormulaParts : Map[PartName, Conjunction] =
    throw new UnsupportedOperationException

  def getAssumedFormulaParts(certificate : Certificate) : Set[PartName] =
    throw new UnsupportedOperationException

  def getPredTranslation : Map[Predicate, IFunction] =
    throw new UnsupportedOperationException

}
