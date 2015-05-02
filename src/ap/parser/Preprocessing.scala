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
import ap.util.Timeout

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
                           Param.GENERATE_TOTALITY_AXIOMS(settings) !=
                             Param.TotalityAxiomOptions.None,
                           signature.functionTypes)
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

    val initialSize = SizeVisitor(f)

    def checkSize(fs : Iterable[IFormula]) = {
      val newSize = (for (f <- fs.iterator) yield SizeVisitor(f)).sum
      if (newSize > 5000000 && newSize > initialSize * 5)
        throw new CmdlMain.GaveUpException("Unexpected explosion during preprocessing")
    }

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
    checkSize(fors2)

    // simple mini-scoping for existential quantifiers
    val miniscoper = new SimpleMiniscoper(signature)
    val fors2a = for (f <- fors2) yield miniscoper(f)

    // compress chains of implications
//    val fors2b = for (INamedPart(n, f) <- fors2a)
//                 yield INamedPart(n, ImplicationCompressor(f))
    
    // check whether we have to add assumptions about the domain size
    val fors2c = Param.FINITE_DOMAIN_CONSTRAINTS(settings) match {
      case Param.FiniteDomainConstraints.DomainSize => {
        import IExpression._
        
        for (f <- fors2a) yield GuardIntroducingVisitor.visit(Transform2NNF(f), 0).asInstanceOf[INamedPart]
      }
      case _ =>
        fors2a
    }
    
    val triggerGenerator =
      new TriggerGenerator (
        Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS(settings),
        Param.TRIGGER_STRATEGY(settings))
    for (f <- fors2c)
      triggerGenerator setup f
    val fors2d =
      for (f <- fors2c) yield triggerGenerator(f)

    // translate functions to relations
    var order3 = signature.order
    val fors3 = for (INamedPart(n, f) <- fors2d) yield INamedPart(n, {
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
    checkSize(fors4)

    // do some direct simplifications
    val fors5 = 
      for (f <- fors4) yield BooleanCompactifier(f).asInstanceOf[INamedPart]
    
    // do clausification
    val fors6 = Param.CLAUSIFIER(settings) match {
      case Param.ClausifierOptions.None =>
        fors5
      case Param.ClausifierOptions.Simple =>
        Timeout.withTimeoutMillis(Param.CLAUSIFIER_TIMEOUT(settings))(
          for (f <- fors5) yield (new SimpleClausifier)(f).asInstanceOf[INamedPart]
        )(throw new CmdlMain.GaveUpException("Clausification timed out"))
    }
    checkSize(fors6)
    
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

////////////////////////////////////////////////////////////////////////////////

private object GuardIntroducingVisitor extends CollectingVisitor[Int, IFormula] {

  import IExpression._
  
  override def preVisit(t : IExpression, quans : Int) : PreVisitResult = t match {
    case LeafFormula(t) =>
      ShortCutResult(t)
    case IQuantified(Quantifier.ALL, _) =>
      UniSubArgs(quans + 1)
    case _ =>
      UniSubArgs(0)
  }
  
  def postVisit(t : IExpression, quans : Int, subres : Seq[IFormula]) : IFormula =
    (t, quans) match {
      case (t@IQuantified(Quantifier.ALL, _), _) =>
        t update subres
      case (t : IFormula, quans) if (quans > 0) => {
        // add guards for the quantified formulae
        val guards = connect(
          for (i <- 0 until quans) yield (v(i) >= 0 & v(i) < CmdlMain.domain_size),
          IBinJunctor.And)
        
        guards ==> (t update subres)
      }
      case (t : IFormula, _) =>
        t update subres
    }
  
}
