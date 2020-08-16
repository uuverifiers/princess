/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.parameters.{PreprocessingSettings, Param}
import ap.theories.{Theory, TheoryRegistry}
import ap.util.Debug

/**
 * Preprocess an InputAbsy formula in order to make it suitable for
 * proving. The result is a list of formulae, because the original formula
 * may contain named parts (<code>INamedPart</code>).
 */
object Preprocessing {
  
  class PreprocessingException(msg : String) extends Exception(msg)

  def apply(f : IFormula,
            interpolantSpecs : List[IInterpolantSpec],
            signature : Signature,
            settings : PreprocessingSettings)
            : (List[INamedPart], List[IInterpolantSpec], Signature) = {
    val funcEnc =
      new FunctionEncoder (Param.TIGHT_FUNCTION_SCOPES(settings),
                           Param.GENERATE_TOTALITY_AXIOMS(settings))
    for (t <- signature.theories)
      funcEnc addTheory t
    apply(f, interpolantSpecs, signature, settings, funcEnc)
  }

  def apply(f : IFormula,
            interpolantSpecs : List[IInterpolantSpec],
            signature : Signature,
            settings : PreprocessingSettings,
            functionEncoder : FunctionEncoder)
            : (List[INamedPart], List[IInterpolantSpec], Signature) = {

    checkSorts("preproc initial", List(f))

    // turn the formula into a list of its named parts
    val fors1a = PartExtractor(f)

    checkSorts("preproc step 1a", fors1a)

    // the other steps can be skipped for simple cases
    if ((functionEncoder.axioms match {
           case IBoolLit(true) => true
           case _ => false
         }) &&
        !needsPreprocessing(fors1a))
      return (fors1a, interpolantSpecs, signature)

    // theory-specific preprocessing
    val (fors1b, signature2) = {
      val theories = signature.theories
      var sig = signature
      val newFors = for (f <- fors1a) yield {
        val (newF, newSig) = Theory.iPreprocess(f, signature.theories, sig)
        sig = newSig
        newF
      }
      (newFors, sig)
    }

    checkSorts("preproc step 1b", fors1b)

    // partial evaluation, expand equivalences
    val fors2a =
      for (f <- fors1b)
      yield EquivExpander(PartialEvaluator(f)).asInstanceOf[INamedPart]

    checkSorts("preproc step 2a", fors2a)

    // mini/maxi-scoping of existential quantifiers
    val fors2b = Param.CLAUSIFIER(settings) match {
      case Param.ClausifierOptions.None | Param.ClausifierOptions.Simple=>
        for (f <- fors2a) yield SimpleMiniscoper(f)
      case Param.ClausifierOptions.ExMaxiscope =>
        for (f <- fors2a) yield ExMaxiscoper(f)
    }

    checkSorts("preproc step 2b", fors2b)

    // compress chains of implications
//    val fors2b = for (INamedPart(n, f) <- fors2a)
//                 yield INamedPart(n, ImplicationCompressor(f))
    
    ////////////////////////////////////////////////////////////////////////////
    // Handling of triggers and encoding of functions

    val (fors3, order3) = {
      val funEncArgs =
        FunctionPreproc.FunctionPreprocArgs(fors2b, signature2.order,
                                            settings, functionEncoder,
                                            signature2.theories)
      val functionEncoding = Param.TRIGGER_GENERATION(settings) match {
        case Param.TriggerGenerationOptions.Complete =>
          new CompleteFunctionPreproc(funEncArgs)
        case Param.TriggerGenerationOptions.CompleteFrugal =>
          new CompleteFrugalFunctionPreproc(funEncArgs)
        case _ =>
          new StdFunctionPreproc(funEncArgs)
      }

      (functionEncoding.newFors, functionEncoding.newOrder)
    }

    checkSorts("preproc step 3", fors3)

    ////////////////////////////////////////////////////////////////////////////
    // Add the function axioms

    val fors4 = functionEncoder.axioms match {
      case IBoolLit(true) => fors3
      case x              => PartExtractor.addPart(x, PartName.NO_NAME, fors3)
    }

    checkSorts("preproc step 4", fors4)

    // do some direct simplifications
    val fors5 = 
      for (f <- fors4) yield BooleanCompactifier(f).asInstanceOf[INamedPart]

    checkSorts("preproc step 5", fors5)

    // do clausification
    val fors6 = Param.CLAUSIFIER(settings) match {
      case Param.ClausifierOptions.None | Param.ClausifierOptions.ExMaxiscope =>
        fors5
      case Param.ClausifierOptions.Simple =>
        for (f <- fors5) yield SimpleClausifier(f).asInstanceOf[INamedPart]
    }

    checkSorts("preproc final", fors6)

    val fors6X = for (f <- fors6) yield VariableSortEliminator(f).asInstanceOf[INamedPart]

    (fors6X.toList, interpolantSpecs, signature2 updateOrder order3)
  }

  private def checkSorts(stage : String, fors : Seq[IFormula]) : Unit = {
    if (Debug.enabledAssertions.value(Debug.AT_METHOD_INTERNAL,
                                      Debug.AC_VAR_TYPES))
      VariableSortChecker(stage, fors)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def needsPreprocessing(fors : List[INamedPart]) : Boolean = try {
    val visitor = new ComplicatedOpVisitor
    for (INamedPart(_, f) <- fors) visitor.visitWithoutResult(f, ())
    false
  } catch {
    case NeedsPreprocException => true
  }

  private object NeedsPreprocException extends Exception

  private class ComplicatedOpVisitor extends CollectingVisitor[Unit, Unit] {
    private var opNum = 0
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = {
      opNum = opNum + 1
      if (opNum > 500)
        throw NeedsPreprocException

      t match {
        case _ : IConstant | _ : IIntLit | _ : IPlus | _ : ITimes |
             _ : IBoolLit | _ : IIntFormula | _ : INot |
             IBinFormula(IBinJunctor.And | IBinJunctor.Or, _, _) =>
          KeepArg
        case IAtom(p, _) if (TheoryRegistry lookupSymbol p).isEmpty =>
          KeepArg
        case _ =>
          throw NeedsPreprocException
      }
    }
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }
}
