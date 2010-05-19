/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

import ap.basetypes.IdealInt
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.proof.ModelSearchProver
import ap.util.{Debug, Seqs}


/**
 * Abstract class providing some functionality commonly needed for
 * interpolation-based software verification, e.g., axioms and prover for
 * bitvector arithmetic, arrays, etc.
 */
abstract class SoftwareInterpolationFramework {

  private val AC = Debug.AC_MAIN

  protected var interpolationProblemBasename = ""
  protected var interpolationProblemNum = 0

  //////////////////////////////////////////////////////////////////////////////
  
  private val preludeEnv = new Environment
  private val functionEncoder = new FunctionEncoder
  
  private val (backgroundPred, preludeOrder) = Console.withOut(Console.err) {
    print("Reading prelude ... ")
    val reader = ResourceFiles.preludeReader
    val (iBackgroundPredRaw, _, signature) = Parser2InputAbsy(reader, preludeEnv)
    reader.close

    val (iBackgroundFors, _, signature2) =
      Preprocessing(iBackgroundPredRaw, List(), signature,
                    PreprocessingSettings.DEFAULT, functionEncoder)
    functionEncoder.clearAxioms
    
    val iBackgroundPred =
      IExpression.connect(for (INamedPart(_, f) <- iBackgroundFors.elements)
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
  
  protected val frameworkVocabulary = new FrameworkVocabulary(preludeEnv)
  import frameworkVocabulary.{select, store}
                                                              
  //////////////////////////////////////////////////////////////////////////////

  private val preprocSettings =
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(PreprocessingSettings.DEFAULT,
                                                     Set(select, store))
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(GoalSettings.DEFAULT, true)
  private val validityCheckSettings =
    GoalSettings.DEFAULT

  protected lazy val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  protected lazy val validityCheckProver = {
    val prover = ModelSearchProver emptyIncProver validityCheckSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val simplifier = new InterpolantSimplifier (select, store)
  
  protected def toInputAbsyAndSimplify(c : Conjunction) : IFormula = {
	val internalInter = Internal2InputAbsy(c, functionEncoder.predTranslation)
//    ap.util.Timer.measure("simplifying") {
      simplifier(internalInter)
//    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  protected def parseProblem(reader : java.io.Reader) = {
    val env = preludeEnv.clone
    val (problem, _, signature) = Parser2InputAbsy(reader, env)

    toNamedParts(problem, signature)
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
  
  protected def toInternal(f : IFormula,
                           sig : Signature) : (Conjunction, TermOrder) = {
    val (parts, sig2) = toNamedParts(f, sig)
    implicit val order = sig2.order
    (disj(for ((_, f) <- parts) yield f), order)
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def dumpInterpolationProblem(transitionParts : Map[PartName, Conjunction],
               	                         sig : Signature) : Unit =
    if (interpolationProblemBasename == "") {
      // nothing to do
    } else {
      import IExpression._
    
      val simpParts =
        for (n <- (if (transitionParts contains PartName.NO_NAME)
                     List(PartName.NO_NAME)
                   else
                     List()) ++
                   sortNamesLex(transitionParts)) yield {
        val f = !transitionParts(n)
        val sf = PresburgerTools.eliminatePredicates(f, !backgroundPred, sig.order)
        INamedPart(n, Internal2InputAbsy(sf, Map()))
      }

      val filename = interpolationProblemBasename + interpolationProblemNum + ".pri"
      interpolationProblemNum = interpolationProblemNum + 1
      
      Console.withOut(new java.io.FileOutputStream(filename)) {
        PrincessLineariser(!connect(simpParts, IBinJunctor.And),
                           sig updateOrder sig.order.resetPredicates)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  protected def genInterpolants(formulas : Seq[Conjunction],
		                        commonFormula : Conjunction,
                                order : TermOrder)
                               : Either[Conjunction, Iterator[Conjunction]] = {
//    ap.util.Timer.measure("solving") {
       interpolationProver.conclude(formulas ++ List(commonFormula), order)
                          .checkValidity(false)
//    }
    match {
      case Left(counterexample) =>
        Left(counterexample)
      case Right(cert) => {
        println("Found proof (size " + cert.inferenceCount + ")")

        Right {
          var lastInterpolant = Conjunction.TRUE
          for (i <- Iterator.range(1, formulas.size)) yield
            if (formulas(i-1).isFalse) {
              // no need to generate a new interpolant, just take the previous
              // one
              lastInterpolant
            } else {
              val iContext =
                InterpolationContext (formulas take i, formulas drop i,
                                      List(commonFormula, backgroundPred),
                                      order)
//              ap.util.Timer.measure("interpolating") {
                lastInterpolant = Interpolator(cert, iContext)
                lastInterpolant
//              }
          }}
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Sort the transition relations lexicographically according to their name
   */
  protected def sortNamesLex(transitionParts : Map[PartName, Conjunction]) : Seq[PartName] = {
    val names = Seqs.toArray((Set() ++ transitionParts.keys) - PartName.NO_NAME)
    Sorting.stableSort(names, (x : PartName, y : PartName) => x.toString < y.toString)
    names
  }

}

////////////////////////////////////////////////////////////////////////////////

object ResourceFiles {

  private val preludeFile = "wolverine_resources/prelude.pri"
//  private val commOpsFile = "/resources/commutativeOperators.list"

  private def toReader(stream : java.io.InputStream) =
    new java.io.BufferedReader (new java.io.InputStreamReader(stream))

  private def resourceAsStream(filename : String) =
//    ResourceFiles.getClass.getResourceAsStream(filename)
    new java.io.FileInputStream(filename)
  
  def preludeReader = toReader(resourceAsStream(preludeFile))
//  def commOpsReader = toReader(resourceAsStream(commOpsFile))
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions
 */
class InterpolantSimplifier(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private class StoreRewriter(depth : Int) {
    var foundProblem : Boolean = false
    var storeArgs : Option[(ITerm, ITerm)] = None

    def rewrite(t : ITerm) : ITerm = t match {
      case IPlus(t1, t2) => rewrite(t1) +++ rewrite(t2)
      case IFunApp(`store`, Seq(IVariable(`depth`), t1, t2)) => {
        if (storeArgs != None)
          foundProblem = true
        storeArgs = Some(shiftVariables(t1), shiftVariables(t2))
        0
      }
      case _ => shiftVariables(t)
    }
    
    private def shiftVariables(t : ITerm) : ITerm = {
      if ((SymbolCollector variables t) contains IVariable(depth))
        foundProblem = true
      VariableShiftVisitor(t, depth + 1, -1)
    }
  }
  
  private def rewriteEquation(t : ITerm, depth : Int) : Option[IFormula] = {
    val rewriter = new StoreRewriter(depth)
    val newT = rewriter rewrite t

    rewriter.storeArgs match {
      case Some((t1, t2)) if (!rewriter.foundProblem) =>
        Some(select(-newT, t1) === t2)
      case _ =>
        None
    }
  }
  
  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = f match {
      
    case IQuantified(q, subF) if (q == (if (negated) ALL else EX)) =>
      for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
        
    case IIntFormula(EqZero, t) if (!negated) =>
      rewriteEquation(t, depth)
    
    case INot(IIntFormula(EqZero, t)) if (negated) =>
      for (f <- rewriteEquation(t, depth)) yield !f
        
    case _ => None
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>  translate(f, false, 0) getOrElse expr
    case IQuantified(ALL, f) => translate(f, true, 0) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}

////////////////////////////////////////////////////////////////////////////////

class FrameworkVocabulary(preludeEnv : Environment) {
  val select = preludeEnv.lookupSym("select") match {
    case Environment.Function(f) => f
    case _ => throw new Error("Expected select to be defined as a function");
  }
  
  val store = preludeEnv.lookupSym("store") match {
    case Environment.Function(f) => f
    case _ => throw new Error("Expected store to be defined as a function");
  }
}
