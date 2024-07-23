/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.parameters.{PreprocessingSettings, Param}
import ap.theories.{Theory, TheoryRegistry}

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap}

object FunctionPreproc {
  case class FunctionPreprocArgs(oldFors : Seq[IFormula],
                                 oldOrder : TermOrder,
                                 settings : PreprocessingSettings,
                                 functionEncoder : FunctionEncoder,
                                 theories : Seq[Theory])
}

/**
 * Class managing the generation of triggers for e-matching, and the
 * encoding of functions using relations. This class is called from
 * <code>Preprocessing</code>.
 */
abstract class FunctionPreproc(args : FunctionPreproc.FunctionPreprocArgs) {
  import args._

  private var order = oldOrder

  protected def encodeFunctions(f : IFormula) : IFormula = {
    val (g, o) = functionEncoder(f, order)
    order = o
    g
  }

  protected val theoryTriggerFunctions =
    (for (t <- theories.iterator;
          f <- t.triggerRelevantFunctions.iterator) yield f).toSet

  // all uninterpreted functions occurring in the problem
  protected val problemFunctions =
    for (f <- FunctionCollector(oldFors);
         if (!(TheoryRegistry lookupSymbol f).isDefined))
    yield f

  protected lazy val allTriggeredFunctions =
    Param.TRIGGER_GENERATION(settings) match {
      case Param.TriggerGenerationOptions.None =>
        theoryTriggerFunctions
      case Param.TriggerGenerationOptions.All =>
        theoryTriggerFunctions ++ problemFunctions
      case _ =>
        theoryTriggerFunctions ++
        (for (g <- problemFunctions.iterator;
              if (!g.partial && !g.relational)) yield g)
    }

  protected lazy val stdTriggerGenerator = {
    val gen = new TriggerGenerator (allTriggeredFunctions,
                                    Param.TRIGGER_STRATEGY(settings))
    for (f <- oldFors)
      gen setup f
    gen
  }

  val newFors : Seq[INamedPart]

  def newOrder : TermOrder = order
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Introduction of triggers according to the chosen
 * <code>-triggerStrategy</code>.
 */
class StdFunctionPreproc(args : FunctionPreproc.FunctionPreprocArgs)
      extends FunctionPreproc(args) {
  import args._

  private val withTriggers =
    for (f <- oldFors) yield stdTriggerGenerator(f)

  val newFors : Seq[INamedPart] =
    for (INamedPart(n, f) <- withTriggers) yield {
      INamedPart(n, encodeFunctions(f))
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Introduction of triggers using the complete strategy that avoids the
 * need for totality axioms (as in Kanger's calculus).
 */
abstract class AbstractCompleteFunctionPreproc(
                 args : FunctionPreproc.FunctionPreprocArgs)
         extends FunctionPreproc(args) {
  import args._

  private val disjuncts =
    (for (INamedPart(n, f) <- oldFors.iterator;
          f2 <- LineariseVisitor(Transform2NNF(f), IBinJunctor.Or).iterator)
     yield (INamedPart(n, f2))).toArray

  private val coll =
    new TotalFunctionCollector(functionEncoder.predTranslation)

  // for each of the disjuncts, determine whether it implies totality of
  // some of the functions
  protected val impliedTotalFunctions =
    for (d@INamedPart(n, f) <- disjuncts) yield {
      if (f.isInstanceOf[IQuantified])
        // translation without triggers
        (d, coll(encodeFunctions(f)) & problemFunctions)
      else
        (d, Set[IFunction]())
    }

  protected val functionOccurrences = new MHashMap[IFunction, Int]
  for ((_, s) <- impliedTotalFunctions.iterator; f <- s.iterator)
    functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)
  
  protected def updateFunctionOccurrences(oldFuns : Set[IFunction],
                                          newDisjunct : IFormula) = {
    for (f <- oldFuns)
      functionOccurrences.put(f, functionOccurrences(f) - 1)
    for (f <- coll(newDisjunct))
      if (problemFunctions contains f)
        functionOccurrences.put(f, functionOccurrences(f) + 1)
  }

  // add the functions for which explicit totality axioms will be created
  if (Param.GENERATE_TOTALITY_AXIOMS(settings))
    for (f <- problemFunctions)
      if (!f.partial)
        functionOccurrences.put(f, functionOccurrences.getOrElse(f, 0) + 1)

  protected val totalFunctions =
    theoryTriggerFunctions ++
    (for (f <- problemFunctions.iterator;
          if ((functionOccurrences get f) match {
                case Some(n) => n > 0
                case None => false
              }))
     yield f)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Introduction of triggers using the complete strategy that avoids the
 * need for totality axioms (as in Kanger's calculus).
 */
class CompleteFunctionPreproc(args : FunctionPreproc.FunctionPreprocArgs)
      extends AbstractCompleteFunctionPreproc(args) {
  import args._

  private val triggeredNonTotal = allTriggeredFunctions -- totalFunctions

  private val newDisjuncts =
    for ((INamedPart(n, disjunct), funs) <- impliedTotalFunctions) yield {
      val withTriggers =
        if (!disjunct.isInstanceOf[IQuantified] ||
              (!ContainsSymbol(disjunct, (f:IExpression) =>
                 f match {
                   case IFunApp(f, _) => triggeredNonTotal contains f
                   case _ => false
                 }) &&
                 !(funs exists { f => functionOccurrences(f) == 1 }))) {
          // can generate triggers for all functions that were identified
          // as total
          stdTriggerGenerator(disjunct)
        } else {
          // add a version of this formula without triggers
          stdTriggerGenerator(disjunct) | disjunct
        }

/*
println(functionOccurrences.toList)
println((INamedPart(n, disjunct), funs))
println(withTriggers)
println()
*/

      val encoded = encodeFunctions(withTriggers)
      updateFunctionOccurrences(funs, encoded)

      INamedPart(n, encoded)
    }

  val newFors = PartExtractor(IExpression.or(newDisjuncts))
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Introduction of triggers using the complete strategy that avoids the
 * need for totality axioms (as in Kanger's calculus).
 */
class CompleteFrugalFunctionPreproc(args : FunctionPreproc.FunctionPreprocArgs)
      extends AbstractCompleteFunctionPreproc(args) {
  import args._

  private val triggerGenerator =
    new TriggerGenerator (totalFunctions,
                          Param.TRIGGER_STRATEGY(settings))
  for (f <- oldFors)
    triggerGenerator setup f

  // only use total functions in triggers
  private val newDisjuncts =
    for ((INamedPart(n, disjunct), funs) <- impliedTotalFunctions) yield {
      val withTriggers =
        if (!disjunct.isInstanceOf[IQuantified] ||
              !(funs exists { f => functionOccurrences(f) == 1 })) {
          // can generate triggers for all functions that were identified
          // as total
          triggerGenerator(disjunct)
        } else {
          // cannot introduce triggers on top-level, since this disjunct
          // is needed to demonstrate totality of some function
          triggerGenerator(EmptyTriggerInjector(disjunct))
        }

      val encoded = encodeFunctions(withTriggers)
      updateFunctionOccurrences(funs, encoded)

/*
println(functionOccurrences.toList)
println((INamedPart(n, disjunct), funs))
println(withTriggers)
println(encoded)
println()
*/

      INamedPart(n, encoded)
    }

  val newFors = PartExtractor(IExpression.or(newDisjuncts))
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
          // TODO: check that the argument variables have the right sorts

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
