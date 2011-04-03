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

package ap;

import ap.proof.{ConstraintSimplifier, ModelSearchProver, Timeout}
import ap.proof.tree.ProofTree
import ap.proof.certificates.Certificate
import ap.terfor.conjunctions.{Conjunction, Quantifier, IterativeClauseMatcher}
import ap.parameters.{GlobalSettings, Param}
import ap.util.{Seqs, Debug}
import ap.interpolants.{Interpolator, InterpolationContext, ProofSimplifier}

object IntelliFileProver {
  
  private val AC = Debug.AC_MAIN
  
  abstract sealed class Result
  
  abstract sealed class ProofResult extends Result
  case class Proof(tree : ProofTree) extends ProofResult
  case class ProofWithModel(tree : ProofTree, model : Conjunction) extends ProofResult
  case class NoProof(unsatisfiableTree : ProofTree) extends ProofResult
  case class TimeoutProof(unfinishedTree : ProofTree) extends ProofResult

  // "model" means that the implicitly existentially quantified constants can be
  // instantiated so that the formula evaluates to true
  abstract sealed class ModelResult extends Result
  case class Model(model : Conjunction) extends ModelResult
  case object NoModel extends ModelResult
  case object TimeoutModel extends ModelResult

  // "countermodel" means that the implicitly universally quantified constants
  // can be instantiated so that the formula evaluates to false
  abstract sealed class CounterModelResult extends Result
  case class CounterModel(counterModel : Conjunction) extends CounterModelResult
  case object NoCounterModel extends CounterModelResult
  case class NoCounterModelCert(certificate : Certificate) extends CounterModelResult
  case class NoCounterModelCertInter(certificate : Certificate,
                                     interpolants : Seq[Conjunction])
             extends CounterModelResult
  case object TimeoutCounterModel extends CounterModelResult
  
}

/**
 * A prover that decides, depending on the kind of the problem, whether it
 * should try to construct a proof tree or just search for counterexamples
 */
class IntelliFileProver(reader : java.io.Reader,
                        // a timeout in milliseconds
                        timeout : Int,
                        mostGeneralConstraint : Boolean,
                        output : Boolean,
                        userDefStoppingCond : => Boolean,
                        settings : GlobalSettings)
      extends AbstractFileProver(reader, output, timeout,
                                 userDefStoppingCond, settings) {

  import IntelliFileProver._

  lazy val proofResult : ProofResult =
    Timeout.catchTimeout[ProofResult] {
      val (tree, validConstraint) = constructProofTree(mostGeneralConstraint)
      if (validConstraint) {
        if (Seqs.disjoint(tree.closingConstraint.constants,
                          signature.universalConstants))
          ProofWithModel(tree, findModel(tree.closingConstraint))
        else
          Proof(tree)
      } else {
        NoProof(tree)
      }
    } {
      // we assume that a partial proof tree is given back
      case x : ProofTree => TimeoutProof(x)
    }
        
  lazy val proofTree : ProofTree = proofResult match {
    case TimeoutProof(t) => t
    case Proof(t) => t
    case ProofWithModel(t, _) => t
    case NoProof(t) => t
  } 

  lazy val modelResult : ModelResult =
    Timeout.catchTimeout[ModelResult] { 
      val model = findModelTimeout.left.get
      if (model.isFalse)
        NoModel
      else
        Model(model)
    } {
      case _ => TimeoutModel
    }

  private def processCert(cert : Certificate) : Certificate = {
    print("Found proof (size " + cert.inferenceCount + ")")
    if (Param.PROOF_SIMPLIFICATION(settings)) {
      print(", simplifying ")
      val simpCert = ProofSimplifier(cert)
      print("(" + simpCert.inferenceCount + ")")
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, simpCert.assumedFormulas subsetOf cert.assumedFormulas)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      simpCert
    } else {
      cert
    }
  }
    
  lazy val counterModelResult : CounterModelResult =
    Timeout.catchTimeout[CounterModelResult] { 
      findCounterModelTimeout match {
        case Left(model) =>
          if (model.isFalse)
            NoCounterModel
          else
            CounterModel(model)
        case Right(cert) if (!interpolantSpecs.isEmpty) => {
          val finalCert = Console.withOut(Console.err) {
            val c = processCert(cert)
            println(", interpolating ...")
            c
          }

          val interpolants = for (spec <- interpolantSpecs.view) yield {
            val iContext = InterpolationContext(namedParts, spec, order)
            Interpolator(finalCert, iContext,
            		     Param.ELIMINATE_INTERPOLANT_QUANTIFIERS(settings))    
          }
          NoCounterModelCertInter(finalCert, interpolants)
        }

        case Right(cert) => {
          val finalCert = Console.withOut(Console.err) {
            val c = processCert(cert)
            println("")
            c
          }
          NoCounterModelCert(finalCert)
        }
      }
    } {
      case _ => TimeoutCounterModel
    }

  val result : IntelliFileProver.Result = {
    val constants =
      Set() ++ (for (f <- formulas.iterator; c <- f.constants.iterator) yield c)
    val quantifiers =
      Set() ++ (for (f <- formulas.iterator;
                     q <- Conjunction.collectQuantifiers(f).iterator) yield q)
    val isFullyMatchable =
      formulas forall (IterativeClauseMatcher isMatchableRec _)

    val canUseModelSearchProver =
      Seqs.disjoint(constants, signature.existentialConstants) &&
      (if (Param.POS_UNIT_RESOLUTION(goalSettings))
         isFullyMatchable
       else
         (quantifiers subsetOf Set(Quantifier.ALL)))
    
    // currently, only the ModelSearchProver can construct proofs
    if (Param.PROOF_CONSTRUCTION(goalSettings) && !canUseModelSearchProver)
      throw new Exception ("Currently no proofs can be constructed for the given" +
                           " problem, since it contains existential constants or" +
                           " quantifiers that cannot be handled by unit resolution")
      
    if ((formulas exists (_.isTrue)) || canUseModelSearchProver) {
      // try to find a countermodel
      counterModelResult
    } else if (!mostGeneralConstraint &&
               (constants subsetOf signature.existentialConstants) &&
               (formulas forall ((f) => f.predicates.isEmpty)) &&
               (quantifiers subsetOf Set(Quantifier.EX))) {
      // try to find a model
      modelResult
    } else {
      // try to construct a proof
      proofResult
    }
  }
  
}
