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
import ap.terfor.conjunctions.Quantifier
import ap.parameters.{PreprocessingSettings, Param}
import ap.theories.TheoryRegistry

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap}

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
    
    ////////////////////////////////////////////////////////////////////////////
    // Handling of triggers

    val theoryTriggerFunctions =
      (for (t <- signature.theories.iterator;
            f <- t.triggerRelevantFunctions.iterator) yield f).toSet
    val problemFunctions =
      for (f <- FunctionCollector(fors2a);
           if (!(TheoryRegistry lookupSymbol f).isDefined))
      yield f

    val fors2c = Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.CompletenessPreserving => {
        val disjuncts =
          (for (INamedPart(n, f) <- fors2a.iterator;
                f2 <- LineariseVisitor(Transform2NNF(f), IBinJunctor.Or).iterator)
           yield (INamedPart(n, f2))).toArray
  
        val coll = new TotalFunctionCollector(functionEncoder.predTranslation)
  
        val impliedTotalFunctions =
          for (d@INamedPart(n, f) <- disjuncts) yield
            if (f.isInstanceOf[IQuantified])
              // translation without triggers
              (d, coll(functionEncoder(f, signature.order)._1) & problemFunctions)
            else
              (d, Set())
  
        val functionOccurrences = new MHashMap[IFunction, Int]
        for ((_, s) <- impliedTotalFunctions.iterator; f <- s.iterator)
          functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)

        // add the functions for which explicit totality axioms will be created
        if (Param.GENERATE_TOTALITY_AXIOMS(settings))
          for (f <- problemFunctions)
            if (!f.partial)
              functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)

        val triggeredFunctions =
          theoryTriggerFunctions ++
          (for (f <- problemFunctions.iterator;
                if ((functionOccurrences get f) match {
                      case Some(n) => n > 0
                      case None => false
                    }))
           yield f)
        val triggerGenerator =
          new TriggerGenerator (triggeredFunctions,
                                Param.TRIGGER_STRATEGY(settings))
        for (f <- fors2a)
          triggerGenerator setup f

        val newDisjuncts =
          for ((INamedPart(n, disjunct), funs) <- impliedTotalFunctions) yield {
//println(functionOccurrences.toList)
//println((INamedPart(n, disjunct), funs))
            val res =
              if (!disjunct.isInstanceOf[IQuantified] ||
                  !(funs exists { f => functionOccurrences(f) == 1 })) {
                // can generate triggers for all functions that were identified
                // as total
                for (f <- funs)
                  functionOccurrences.put(f, functionOccurrences(f) - 1)
                triggerGenerator(disjunct)
              } else {
                // cannot introduce triggers on top-level, since this disjunct
                // is needed to demonstrate totality of some function
                triggerGenerator(EmptyTriggerInjector(disjunct))
              }
 
//println(res)
            INamedPart(n, res)
          }
  
        PartExtractor(IExpression.or(newDisjuncts))
      }

      case gen => {
        val triggeredFunctions = gen match {
          case Param.TriggerGenerationOptions.None =>
            theoryTriggerFunctions
          case Param.TriggerGenerationOptions.All =>
            theoryTriggerFunctions ++ problemFunctions
          case Param.TriggerGenerationOptions.Total =>
            theoryTriggerFunctions ++
            (for (g <- problemFunctions.iterator;
                  if (!g.partial && !g.relational)) yield g)
        }

        val triggerGenerator =
          new TriggerGenerator (triggeredFunctions,
                                Param.TRIGGER_STRATEGY(settings))
        for (f <- fors2a)
          triggerGenerator setup f

        for (f <- fors2a) yield triggerGenerator(f)
      }
    }

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

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor that determines functions whose totality is implied by a
 * quantified formula.
 */
private class TotalFunctionCollector(
        predTranslation : scala.collection.Map[IExpression.Predicate, IFunction])
              extends ContextAwareVisitor[Unit, Unit] {

  private val collectedFunctions = new MHashSet[IFunction]

  def apply(f : IFormula) : Set[IFunction] = {
    this.visitWithoutResult(f, Context(()))
    val res = collectedFunctions.toSet
    collectedFunctions.clear
    res
  }

  override def preVisit(t : IExpression,
                        ctxt : Context[Unit]) : PreVisitResult = t match {
    case _ : IQuantified | _ : INot =>
      super.preVisit(t, ctxt)
    case IBinFormula(IBinJunctor.And, _, _)
      if (ctxt.polarity < 0) =>
        super.preVisit(t, ctxt)
    case IBinFormula(IBinJunctor.Or, _, _)
      if (ctxt.polarity > 0) =>
        super.preVisit(t, ctxt)

    case IAtom(p, args)
      if (ctxt.polarity < 0) => (predTranslation get p) match {
        case Some(f) => {
          // the function arguments have to be existentially quantified

          val exIndexes =
            (for (IVariable(ind) <- args.init.iterator;
                  if (ctxt.binders(ind) == Context.EX))
             yield ind).toSet
          if (exIndexes.size == args.size - 1)
            collectedFunctions += f

          ShortCutResult(())
        }
        case None =>
          ShortCutResult(())
      }
    case _ =>
      ShortCutResult(())
  }

  def postVisit(t : IExpression, ctxt : Context[Unit],
                subres : Seq[Unit]) : Unit = ()

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor to add an empty trigger set for every top-level existential
 * quantifier. This assumes that the given formula is in NNF.
 */
private object EmptyTriggerInjector
        extends CollectingVisitor[Boolean, IExpression] {

  def apply(f : IFormula) : IFormula =
    this.visit(f, false).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        underEx : Boolean) : PreVisitResult = t match {
    case IQuantified(Quantifier.EX, _) =>
      UniSubArgs(true)
    case _ : IQuantified |
         IBinFormula(IBinJunctor.Or, _, _) |
         _ : ITrigger =>
      UniSubArgs(false)
    case t : IFormula =>
      ShortCutResult(if (underEx) ITrigger(List(), t) else t)
  }

  def postVisit(t : IExpression, underEx : Boolean,
                subres : Seq[IExpression]) : IExpression = t match {
    case _ : ITrigger | IQuantified(Quantifier.EX, _) =>
      t update subres
    case t : IFormula if (underEx) =>
      ITrigger(List(), t update subres)
    case t =>
      t update subres
  }

}