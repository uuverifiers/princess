/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.interpolants

import scala.util.Sorting
import scala.collection.mutable.{ArrayStack => MStack,
                                 Map => MMap, HashMap => MHashMap}

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier,
                               SetEliminator}
import ap.terfor.TerForConvenience._
import ap.terfor.{TermOrder, ConstantTerm}
import ap.proof.ModelSearchProver
import ap.util.{Debug, Seqs}

object BAPAFramework {
  
  private val AC = Debug.AC_BAPA

  //////////////////////////////////////////////////////////////////////////////
  
  object BAPAResourceFiles {

    private val preludeFile = "bapa_resources/prelude.pri"

    private def toReader(stream : java.io.InputStream) =
      new java.io.BufferedReader (new java.io.InputStreamReader(stream))

    private def resourceAsStream(filename : String) =
      //    ResourceFiles.getClass.getResourceAsStream(filename)
      new java.io.FileInputStream(filename)
  
    def preludeReader = toReader(resourceAsStream(preludeFile))
  }

  //////////////////////////////////////////////////////////////////////////////

  class BAPAFrameworkVocabulary(preludeEnv : Environment)
        extends AbstractFrameworkVocabulary(preludeEnv) {
    val union =           lookupFun("union")
    val intersection =    lookupFun("intersection")
    val complementation = lookupFun("complementation")
    val size =            lookupFun("size")
    val difference =      lookupFun("difference")
    val singleton =       lookupFun("singleton")
    val emptySet =        lookupConst("emptySet")
  
    val subsetOf =        lookupPred("subsetOf")
    val setEq =           lookupPred("setEq")
    val isEmpty =         lookupPred("isEmpty")
    val inSet =           lookupPred("inSet")
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Abstract class providing some functionality for checking and interpolating
 * problems in BAPA
 */
class BAPAFramework {

  import BAPAFramework._
  
  private val preludeEnv = new Environment
  private val functionEncoder =
    new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(PreprocessingSettings.DEFAULT),
                         false)
  
  private val (backgroundPred, preludeOrder) = Console.withOut(Console.err) {
    print("Reading prelude ... ")
    val reader = BAPAResourceFiles.preludeReader
    val (iBackgroundPredRaw, _, signature) =
      new ApParser2InputAbsy(preludeEnv)(reader)
    reader.close

    val (iBackgroundFors, _, signature2) =
      Preprocessing(iBackgroundPredRaw, List(), signature,
                    PreprocessingSettings.DEFAULT, functionEncoder)
    functionEncoder.clearAxioms
    
    val iBackgroundPred =
      IExpression.connect(for (INamedPart(_, f) <- iBackgroundFors.iterator)
                            yield f,
                          IBinJunctor.Or)
    implicit val order = signature2.order
    
    val res = InputAbsy2Internal(iBackgroundPred, order)
    
    // we put the (possibly extended) order back into the environment, so that
    // we can continue parsing the transition relations with it
    preludeEnv.order = order

    val reducedRes = ReduceWithConjunction(Conjunction.TRUE, order)(conj(res))
    
    println("done")
    (reducedRes, order)
  }
  
  protected val preludeSignature = preludeEnv.toSignature
  
  //////////////////////////////////////////////////////////////////////////////
  
  val vocabulary = new BAPAFrameworkVocabulary(preludeEnv)
  import vocabulary._

  private val preprocSettings =
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(PreprocessingSettings.DEFAULT,
       Set(singleton, union, intersection, difference, size, complementation))

  private val satCheckSettings = {
    var s = GoalSettings.DEFAULT
    s = Param.FUNCTIONAL_PREDICATES.set(s, backgroundPred.predicates)
    
    // now the function encoder contains the predicates that functions
    // are translated to
    def predForFun(f : IFunction) = (functionEncoder.predTranslation.find {
      case (_, `f`) => true
      case _ => false
    }).get._1
    
    val setPredicates =
      SetEliminator.SetPredicates(predForFun(intersection),
                                  predForFun(union),
                  predForFun(complementation),
                  emptySet)
    
    s = Param.SET_PREDICATES.set(s, Some(setPredicates))
    s
  }
  
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(satCheckSettings, true)

  protected lazy val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  protected lazy val satCheckProver = {
    val prover = ModelSearchProver emptyIncProver satCheckSettings
    prover.conclude(backgroundPred, preludeOrder)
  }

  //////////////////////////////////////////////////////////////////////////////
    
  private val interpolantSimplifier = new Simplifier
  
  protected def toInputAbsyAndSimplify(c : Conjunction) : IFormula = {
    val internalInter = Internal2InputAbsy(c, functionEncoder.predTranslation)
//    ap.util.Timer.measure("simplifying") {
      interpolantSimplifier(internalInter)
//    }
  }

  protected def toInternal(f : IFormula,
                           sig : Signature) : (Conjunction, TermOrder) = {
    val (parts, sig2) = toNamedParts(f, sig)
    implicit val order = sig2.order
    (disj(for ((_, f) <- parts) yield f), order)
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def parseProblem(reader : java.io.Reader) : (IFormula, Signature) = {
    val (problem, _, sig) = new ApParser2InputAbsy(preludeEnv.clone)(reader)
    (problem, sig)
  }

  protected def toNamedParts(f : IFormula, sig : Signature) = {
    val (iProblemParts, _, sig2) =
      Preprocessing(f, List(), sig, preprocSettings, functionEncoder)
    functionEncoder.clearAxioms
    implicit val order = sig2.order
    
    val namedParts =
      Map() ++ (for (INamedPart(name, f) <- iProblemParts)
                yield (name -> conj(InputAbsy2Internal(f, order))))

    (namedParts, sig2)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  protected def parseAndConvert(input : java.io.Reader)
                                : (Map[PartName, Conjunction], Signature) = {
    import IExpression._
    import IBinJunctor._
    
    val (problem, signature) = parseProblem(input)
    toNamedParts(problem, signature)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Checking satisfiability of a formula
  
  def isSat(problem : IFormula, constants : Seq[ConstantTerm]) : Boolean = {
    // signature of the problem
    val order = preludeOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, _, signature2) =
      Preprocessing(!problem,
                    List(),
                    signature,
                    preprocSettings,
                    functionEncoder)
    val order2 = signature2.order
    //println("sat check: " + problem)

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == IExpression.i(true))
    
    // convert to internal representation
    val formulas =
      for (f <- inputFormulas) yield
        Conjunction.conj(InputAbsy2Internal(IExpression.removePartName(f), order2),
                         order2)

    satCheckProver.conclude(formulas, order2)
                  .checkValidity(false) != Left(Conjunction.FALSE)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing model of formulae

  def findModel(problem : IFormula,
                constants : Seq[ConstantTerm]) : Option[IFormula] = {
    // signature of the problem
    val order = preludeOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, _, signature2) =
      Preprocessing(!problem,
                    List(),
                    signature,
                    preprocSettings,
                    functionEncoder)
    val order2 = signature2.order

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == IExpression.i(true))
    
    // convert to internal representation
    val formulas =
      for (f <- inputFormulas) yield
        Conjunction.conj(InputAbsy2Internal(IExpression.removePartName(f), order2),
                         order2)

    satCheckProver.conclude(formulas, order2).checkValidity(true) match {
      case Left(Conjunction.FALSE) =>
        // unsat
        None
      case Left(model) =>
        // found a model
        Some((new Simplifier)(
          Internal2InputAbsy(model, functionEncoder.predTranslation)))
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Constructing interpolants of formulae

  def interpolate(problem : IFormula,
                  constants : Seq[ConstantTerm],
                  partitions : List[IInterpolantSpec]) : Option[List[IFormula]] = {
    // signature of the problem
    val order = preludeOrder extend constants
    val signature = new Signature(constants.toSet, Set(), Set(), order)
    
    // preprocessing: e.g., encode functions as predicates
    val (inputFormulas, interpolantS, signature2) =
      Preprocessing(!problem,
                    partitions,
                    signature,
                    PreprocessingSettings.DEFAULT,
                    functionEncoder)
    val order2 = signature2.order

    // we currently assume that problems don't introduce new functions
    assert(functionEncoder.axioms == IExpression.i(true))
    //println("Interpolation: " + problem)
    //println(constants)

    // convert to internal representation, pre-simplify
    val formulas =
      for (f <- inputFormulas) yield
        ReduceWithConjunction(Conjunction.TRUE, order2)(
          Conjunction.conj(InputAbsy2Internal(IExpression.removePartName(f), order2),
                           order2))                           

    interpolationProver.conclude(formulas, order2).checkValidity(false) match {
      case Left(_) =>
        // formula is sat
        None
      
      case Right(cert) => {
        // found a proof of unsatisfiability, extract an interpolant

        //print("Found proof (" + cert.inferenceCount + "), simplifying ")
        val simpCert = ProofSimplifier(cert) // simplify the proof if possible
        //println("(" + simpCert.inferenceCount + ")")

        val namedParts =
          (for ((INamedPart(name, _), f) <- inputFormulas zip formulas)
           yield (name -> f)).toMap + (PartName.NO_NAME -> backgroundPred)
        
        Some(for (s <- interpolantS) yield {
          val iContext = InterpolationContext(namedParts, s, order2)
          toInputAbsyAndSimplify(Interpolator(simpCert, iContext, true))
        })
      }
    }
  }

}
