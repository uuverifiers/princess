/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap;

import ap.basetypes.IdealInt
import ap.parser.{ContainsSymbol, IExpression, IAtom, IFunApp}
import ap.proof.{ConstraintSimplifier, ModelSearchProver}
import ap.proof.tree.ProofTree
import ap.proof.certificates.{Certificate, DagCertificateConverter}
import ap.terfor.conjunctions.{Conjunction, Quantifier, IterativeClauseMatcher}
import ap.theories.TheoryRegistry
import ap.parameters.{GlobalSettings, Param}
import ap.util.{Seqs, Debug, Timeout}
import ap.interpolants.{Interpolator, InterpolationContext, ProofSimplifier}

object IntelliFileProver {
  
  private val AC = Debug.AC_MAIN
  
}

/**
 * A prover that decides, depending on the kind of the problem, whether it
 * should try to construct a proof tree or just search for counterexamples
 */
class IntelliFileProver(reader   : java.io.Reader,
                        timeout  : AbstractFileProver.TimeoutCondition,
                        output   : Boolean,
                        userDefStoppingCond : => Boolean,
                        settings : GlobalSettings)
      extends AbstractFileProver(reader, output, timeout,
                                 userDefStoppingCond, settings) {

  import Prover._

  private val posUnitResolution = Param.POS_UNIT_RESOLUTION(settings)

  // are only theories used for which we can also reason about the
  // negated formula?
  private lazy val onlyCompleteTheories = rawSignature.theories forall {
    case ap.types.TypeTheory                => true
    case _ : ap.theories.MulTheory          => true
    case _ : ap.theories.IntValueEnumTheory => true
    case ap.theories.ModuloArithmetic       => posUnitResolution
    // strictly speaking, only works for guarded formulas in ADT ... (TODO!)
    case _ : ap.theories.ADT                => posUnitResolution
    case _                                  => false
  }

  // only theories for which quantifier elimination is implemented?
  private lazy val onlyQEEnabledTheories = rawSignature.theories forall {
    case ap.types.TypeTheory                => true
    case _ : ap.theories.MulTheory          => true
    case _ : ap.theories.IntValueEnumTheory => true
    case ap.theories.ModuloArithmetic       => posUnitResolution
    case _                                  => false
  }

  // is the problem free of uninterpreted Boolean variables?
  // (nullary predicates)
  private lazy val noBooleanVars =
    !ContainsSymbol(rawInputFormula, (e:IExpression) => e match {
      case IAtom(p, _)   => (TheoryRegistry lookupSymbol p).isEmpty
      case _             => false
    })

  // do all function or predicate symbols (with arguments) in the raw input
  // formula belong to a theory?
  private lazy val onlyInterpretedSymbols = 
    !ContainsSymbol(rawInputFormula, (e:IExpression) => e match {
      case IAtom(p, _)   => p.arity > 0 &&
                            (TheoryRegistry lookupSymbol p).isEmpty
      case IFunApp(f, _) => (TheoryRegistry lookupSymbol f).isEmpty
      case _             => false
    })

  // does the input formula contain functions or predicates?
  private lazy val containsFunctionsPreds = 
    ContainsSymbol(rawInputFormula, (e:IExpression) => e match {
      case IFunApp(f, _) => true
      case IAtom(p, _)   => p.arity > 0
      case _             => false
    })

  private lazy val onlyExistentialConstsVars =
    (rawConstants subsetOf rawSignature.existentialConstants) &&
    (rawQuantifiers subsetOf Set(Quantifier.EX)) &&
    noBooleanVars

  private lazy val canUseNegatedSolving =
    !constructProofs &&
    onlyCompleteTheories &&
    onlyInterpretedSymbols &&
    (!Param.MOST_GENERAL_CONSTRAINT(settings) ||
       (onlyQEEnabledTheories && noBooleanVars)) &&
    (onlyExistentialConstsVars || onlyQEEnabledTheories)

  private lazy val preferNegatedSolving =
    Param.NEG_SOLVING(settings) match {
      case Param.NegSolvingOptions.Positive =>
        false
      case Param.NegSolvingOptions.Negative =>
        true
      case Param.NegSolvingOptions.Auto =>
        //
        // purely existential formulas can best be handled by negation
        ((!rawConstants.isEmpty || rawQuantifiers.contains(Quantifier.EX)) &&
         onlyExistentialConstsVars) ||
        //
        // formulas in the forall-exists fragment can also be handled better
        // by negation
        (onlyQEEnabledTheories &&
         (rawConstants subsetOf rawSignature.nullaryFunctions) &&
         (rawQuantifiers contains Quantifier.EX) &&
         containsFunctionsPreds &&
         AllExVisitor(rawInputFormula) &&
         (!rawConstants.isEmpty ||
          !(rawQuantifiers contains Quantifier.ALL) ||
          !AllExVisitor(~rawInputFormula)))
    }

  // do we work with the positive or negative input formula?
  val (usedTranslation, usingNegatedFormula) =
    if (canUseNegatedSolving && preferNegatedSolving) {
      // try to find a model of the negated formula
      (negTranslation, true)
    } else {
      // work positively
      if (Param.NEG_SOLVING(settings) == Param.NegSolvingOptions.Negative)
        Console.err.println("Warning: ignoring option -formulaSign=negative")
      (posTranslation, false)
    }

  // currently, only the ModelSearchProver can construct proofs
  if (usedTranslation != null &&
        Param.PROOF_CONSTRUCTION(usedTranslation.goalSettings) &&
        !usedTranslation.canUseModelSearchProver)
    throw new Exception (
      "Currently no proofs can be constructed for the given" +
      " problem,\nsince it contains existential constants or" +
      " quantifiers that cannot be\nhandled by unit resolution.\n" +
      "You might want to use the option -genTotalityAxioms")

  //////////////////////////////////////////////////////////////////////////////

  lazy val proofResult : ProofResult =
    Timeout.catchTimeout[ProofResult] {
      import posTranslation._
      val (tree, validConstraint) = constructProofTree("Proving")
      if (validConstraint) {
        if (Seqs.disjoint(tree.closingConstraint.constants,
                          transSignature.universalConstants) &&
            !transSignature.existentialConstants.isEmpty &&
            Param.COMPUTE_MODEL(settings))
          ProofWithModel(tree,
                         processConstraint(tree.closingConstraint),
                         processConstraint(findModel(tree.closingConstraint)))
        else
          Proof(tree, processConstraint(tree.closingConstraint))
      } else if (soundForSat) {
        Invalid(tree)
      } else {
        NoProof(tree)
      }
    } {
      case x : ProofTree => TimeoutProof(x)
      case _ => TimeoutProof(null)
    }

  lazy val negProofResult : ProofResult =
    Timeout.catchTimeout[ProofResult] {
      import negTranslation._
      val (tree, validConstraint) =
        constructProofTree("Proving negated formula")
      if (validConstraint) {
        Invalid(tree)
      } else if (soundForSat) {
        Proof(tree, ap.parser.IBoolLit(true))
      } else {
        NoProof(tree)
      }
    } {
      case x : ProofTree => TimeoutProof(x)
      case _ => TimeoutProof(null)
    }

  lazy val proofTree : ProofTree = proofResult match {
    case TimeoutProof(t) => t
    case Proof(t, _) => t
    case ProofWithModel(t, _, _) => t
    case NoProof(t) => t
    case Invalid(t) => t
  }

  lazy val modelResult : ModelResult =
    Timeout.catchTimeout[ModelResult] { 
      import negTranslation._
      if (Param.MOST_GENERAL_CONSTRAINT(settings)) {
        val (tree, _) =
          constructProofTree("Eliminating quantifiers")
       val mgConstraint = tree.closingConstraint.negate
       if (mgConstraint.isFalse) {
         NoModel
       } else {
         val constraint =
           Param.MGC_FORMAT(settings) match {
             case Param.MGCFormatOptions.Any =>
               mgConstraint
             case Param.MGCFormatOptions.DNF =>
               Conjunction.disj(
                 PresburgerTools.nonDNFEnumDisjuncts(mgConstraint), order)
             case Param.MGCFormatOptions.CNF =>
               !Conjunction.disj(
                 PresburgerTools.nonDNFEnumDisjuncts(!mgConstraint), order)
           }
         AllModels(processConstraint(constraint),
                   if (Param.COMPUTE_MODEL(settings))
                     Some(processModel(findModel(mgConstraint)))
                   else
                     None)
       }
      } else {
        val model = findModelTimeout.left.get
        if (model.isFalse)
          NoModel
        else
          Model(if (Param.COMPUTE_MODEL(settings))
                  Some(processModel(model))
                else
                  None)
      }
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
      Debug.assertInt(IntelliFileProver.AC,
                      simpCert.assumedFormulas subsetOf cert.assumedFormulas)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      simpCert
    } else {
      cert
    }
  }

/*
  private def processCert(cert : Certificate) : Certificate = {
    print("Found proof (size " + cert.inferenceCount)
    val dagCert = DagCertificateConverter(cert)
    print(", dag-size " + (DagCertificateConverter size dagCert) + ")")
    if (Param.PROOF_SIMPLIFICATION(settings)) {
      print(", simplifying ")
      val simpDagCert = ProofSimplifier(dagCert)
      print("(dag-size " + (DagCertificateConverter size simpDagCert) + ")")
      val res = DagCertificateConverter inline simpDagCert
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(IntelliFileProver.AC,
                      res.assumedFormulas subsetOf cert.assumedFormulas)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    } else {
      cert
    }
  }
  */
  
  lazy val counterModelResult : CounterModelResult =
    Timeout.catchTimeout[CounterModelResult] {
      import posTranslation._

      findCounterModelTimeout match {
        case Left(model) =>
          if (model.isFalse) {
            NoCounterModel
          } else {
            val optModel =
              if (Param.COMPUTE_MODEL(settings))
                Some(processModel(model))
              else
                None

            if (soundForSat)
              CounterModel(optModel)
            else
              MaybeCounterModel(optModel)
          }
        case Right(cert) if (!preprocInterpolantSpecs.isEmpty) => {
          val finalCert = Console.withOut(Console.err) {
            val c = processCert(cert)
            println(", interpolating ...")
            c
          }

          val interpolants = for (spec <- preprocInterpolantSpecs.view) yield {
            val iContext = InterpolationContext(namedParts, spec, order)
            val rawInterpolant =
              Interpolator(finalCert, iContext,
                           Param.ELIMINATE_INTERPOLANT_QUANTIFIERS(settings),
                           Param.REDUCER_SETTINGS(goalSettings))
            processInterpolant(rawInterpolant)
          }
          NoCounterModelCertInter(cert, interpolants)
        }

        case Right(cert) => {
          Console.err.println("Found proof (size " + cert.inferenceCount + ")")
/*
          val finalCert = Console.withOut(Console.err) {
            val c = processCert(cert)
            println("")
            c
          }
 */
          NoCounterModelCert(cert)
        }
      }
    } {
      case _ => TimeoutCounterModel
    }

  //////////////////////////////////////////////////////////////////////////////

  val result : Prover.Result = {
    if (usedTranslation == null) {
      TimeoutProof(null)
    } else if (usingNegatedFormula) {
      if (onlyExistentialConstsVars)
        // try to find a model
        modelResult
      else
        // try to construct a proof
        negProofResult
    } else if (usedTranslation.canUseModelSearchProver) {
      // try to find a countermodel
      counterModelResult
    } else  {
      // try to construct a proof
      proofResult
    }
  }
  
}
