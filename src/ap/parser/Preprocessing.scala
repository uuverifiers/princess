/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parameters.{PreprocessingSettings, Param}

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

    // turn the formula into a list of its named parts
    val fors = PartExtractor(f)

    // the other steps can be skipped for simple cases
    if ((functionEncoder.axioms match {
           case IBoolLit(true) => true
           case _ => false
         }) &&
        !needsPreprocessing(fors))
      return (fors, interpolantSpecs, signature)

    // partial evaluation, expand equivalences
    val fors2 =
      for (f <- fors)
      yield EquivExpander(PartialEvaluator(f)).asInstanceOf[INamedPart]

    // simple mini-scoping for existential quantifiers
    val fors2a = for (f <- fors2) yield SimpleMiniscoper(f)

    // compress chains of implications
//    val fors2b = for (INamedPart(n, f) <- fors2a)
//                 yield INamedPart(n, ImplicationCompressor(f))
    
    val triggerGenerator =
      new TriggerGenerator (
        Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS(settings),
        Param.TRIGGER_STRATEGY(settings))
    for (f <- fors2a)
      triggerGenerator setup f
    val fors2c =
      for (f <- fors2a) yield triggerGenerator(f)

    // translate functions to relations
    var order3 = signature.order
    val fors3 = for (INamedPart(n, f) <- fors2c) yield INamedPart(n, {
      val (g, o) = functionEncoder(f, order3)
      order3 = o
      g
    })
    
    // add the function axioms
    val fors4 = functionEncoder.axioms match {
      case IBoolLit(true) => fors3
      case x => {
        var noNamePart : INamedPart = null
        var realNamedParts : List[INamedPart] = List()
        
        for (p @ INamedPart(n, _) <- fors3)
          if (n == PartName.NO_NAME)
            noNamePart = p
          else
            realNamedParts = p :: realNamedParts
        
        val newNoNamePart = noNamePart match {
          case null => INamedPart(PartName.NO_NAME, !x)
          case INamedPart(_, f) => INamedPart(PartName.NO_NAME, f | !x)
        }
        newNoNamePart :: realNamedParts
      }
    }

    // do some direct simplifications
    val fors5 = 
      for (f <- fors4) yield BooleanCompactifier(f).asInstanceOf[INamedPart]
    
    // do clausification
    val fors6 = Param.CLAUSIFIER(settings) match {
      case Param.ClausifierOptions.None =>
        fors5
      case Param.ClausifierOptions.Simple =>
        for (f <- fors5) yield SimpleClausifier(f).asInstanceOf[INamedPart]
    }
    
    (fors6, interpolantSpecs, signature updateOrder order3)
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
             _ : IAtom | _ : IBoolLit | _ : IIntFormula | _ : INot |
             IBinFormula(IBinJunctor.And | IBinJunctor.Or, _, _) => KeepArg
        case _ => throw NeedsPreprocException
      }
    }
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }
  
}
