/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import scala.collection.mutable.{Map => MMap, HashMap => MHashMap}

import ap.terfor.{TermOrder, ConstantTerm, VariableTerm}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs}

object FunctionEncoder2 {

  private val AC = Debug.AC_INPUT_ABSY
  
  import IExpression._

  
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to generate a relational encoding of functions. This means that
 * an (n+1)-ary predicate is introduced for each n-ary function, together
 * with axioms for totality and functionality, and that all applications of the
 * function are replaced referring to the predicate. The state of the class
 * consists of the mapping from functions to relations (so far), as well as
 * the axioms that have been introduced for the relational encoding.
 */
class FunctionEncoder2 {
  
  import FunctionEncoder._
  import IExpression._
  
  def apply(f : IFormula, order : TermOrder) : (IFormula, TermOrder) = {
    val nnfF = Transform2NNF(f)
    
    val freeVars = SymbolCollector variables nnfF
    val visitor = new EncoderVisitor(order)
    val context : Context[EncodingContext] = Context(EncodingContext(false))
    
    val newF = visitor.visit(nnfF, context).asInstanceOf[IFormula]
    ////////////////////////////////////////////////////////////////////////////
    // no dangling variables in the result
    Debug.assertInt(FunctionEncoder2.AC,
                    Set() ++ (SymbolCollector variables newF) == Set() ++ freeVars)
    ////////////////////////////////////////////////////////////////////////////
    (newF, visitor.order)
  }

  // axioms for totality and functionality of the predicates
  def axioms = axiomsVar
  def clearAxioms = {
    axiomsVar = true
  }
  
  private var axiomsVar : IFormula = true
  
  //////////////////////////////////////////////////////////////////////////////

  // map with all predicates that are used to encode functions
  private val relations =
    new scala.collection.mutable.HashMap[IFunction, Predicate]
  
  private def totality(pred : Predicate) : IFormula = {
    val args = (for (i <- 1 until pred.arity) yield v(i)) ++ List(v(0))
    val atom = IAtom(pred, args)
    quan(List.make(pred.arity - 1, Quantifier.ALL), ex(atom))
  }
  
  private def functionality(pred : Predicate) : IFormula = {
    val baseArgs = for (i <- 0 until (pred.arity - 1)) yield v(i)
    val atom1 = IAtom(pred, baseArgs ++ List(v(pred.arity - 1)))
    val atom2 = IAtom(pred, baseArgs ++ List(v(pred.arity)))
    val matrix = atom1 -> (atom2 -> (v(pred.arity - 1) === v(pred.arity)))
    quan(List.make(pred.arity + 1, Quantifier.ALL), matrix)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * During the abstraction, instead of variables and de Brujin indexes we use
   * unique constants. The following map maps variable indexes (on the
   * top level) to the corresponding constants.
   */
  private val varConstants = new MHashMap[Int, ConstantTerm]
  
  private def constantForVar(index : Int, binderLevel : Int) : ConstantTerm =
    varConstants.getOrElseUpdate(index - binderLevel,
                                 new ConstantTerm ("varConst"))
  
  private val funAppConstants = new MHashMap[IFunApp, ConstantTerm]

  private def constantForApp(app : IFunApp) : ConstantTerm = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(FunctionEncoder2.AC,
                    !app.strong && (SymbolCollector variables app).isEmpty)
    ////////////////////////////////////////////////////////////////////////////
    funAppConstants.getOrElseUpdate(app, new ConstantTerm ("appConst"))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  case class EncodingContext(underneathFunctionApp : Boolean)

  object AbstractionResult {
    def merge(results : Iterable[AbstractionResult],
              mixedToStrong : Boolean) : AbstractionResult = {
      val allStrongApps =
        Set() ++ (for (r <- results.elements;
                       x <- r.strongApps.elements) yield x)
      val allWeakApps =
        Set() ++ (for (r <- results.elements;
                       x <- r.weakApps.elements) yield x)
      
      if (mixedToStrong)
        AbstractionResult(allWeakApps -- allStrongApps, allStrongApps)
      else
        AbstractionResult(allWeakApps, allStrongApps -- allWeakApps)
    }
    
    val EMPTY = AbstractionResult(Set(), Set())
  }
  
  case class AbstractionResult(weakApps : Set[IAtom], strongApps : Set[IAtom]) {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertCtor(FunctionEncoder2.AC, Seqs.disjoint(weakApps, strongApps))
    ////////////////////////////////////////////////////////////////////////////
    
    def merge(that : AbstractionResult,
              mixedToStrong : Boolean) : AbstractionResult =
      AbstractionResult.merge(List(this, that), mixedToStrong)
    
    def add(app : IAtom, strong : Boolean) : AbstractionResult =
      if (strong)
        AbstractionResult(weakApps, strongApps + app)
      else
        AbstractionResult(weakApps + app, strongApps)
  }
  
  /**
   * Visitor to relationally encode all function applications in an expression.
   * The result of the visitor is a set of weak function applications that
   * have been replaced with constants, a set of strong function applications
   * replaced with constants, and the resulting expression.
   */
  private class EncoderVisitor(var order : TermOrder)
                extends ContextAwareVisitor[EncodingContext,
                                            (AbstractionResult, IExpression)] {
  
    private def toRelation(fun : IFunction) : Predicate = 
      relations.getOrElseUpdate(fun, {
        val pred = new Predicate(fun.name, fun.arity + 1)
        order = order extend pred
        if (!fun.relational)
          axiomsVar = axiomsVar &&& functionality(pred)
        if (!fun.partial)
          axiomsVar = axiomsVar &&& totality(pred)
        pred
      })

    override def preVisit(t : IExpression, c : Context[EncodingContext])
                                                : PreVisitResult = t match {
      case INot(sub) => {
        ////////////////////////////////////////////////////////////////////////
        // we assume that the formula is in negation normal form
        Debug.assertPre(FunctionEncoder2.AC, LeafFormula.unapply(sub) != None)
        ////////////////////////////////////////////////////////////////////////
        super.preVisit(t, c)
      }
      case _ : IFunApp =>
        UniSubArgs(c(EncodingContext(true)))
      case _ =>
        super.preVisit(t, c)
    }

    ////////////////////////////////////////////////////////////////////////////

    def postVisit(t : IExpression, c : Context[EncodingContext],
                  subres : Seq[(AbstractionResult, IExpression)])
                 : (AbstractionResult, IExpression) = t match {
      case IFunApp(f, strong, _) => {
        assert(!f.relational) // todo
        
        val newArgs = for (r <- subres) yield (r._2).asInstanceOf[ITerm]
        val normalisedApp = IFunApp(f, false, newArgs)
        val abstractExpr = constantForApp(normalisedApp)
        val abstractDef = IAtom(toRelation(f), newArgs ++ List(abstractExpr))
        
        (AbstractionResult.merge(for (r <- subres) yield (r._1), true)
                          .add(abstractDef, strong),
         abstractExpr)
      }

      case _ : IAtom => {
        val (abs, newArgs) = Seqs unzip subres
        (AbstractionResult.merge(abs, true), t update newArgs)
      }
      
      case IVariable(index) if (c.a.underneathFunctionApp) =>
        (AbstractionResult.EMPTY, constantForVar(index, c.quans.size))
        
      case IBinFormula(j, _, _) => {
        ////////////////////////////////////////////////////////////////////////
        // assume that no equivalences occur anymore
        Debug.assertInt(FunctionEncoder2.AC,
                        j == IBinJunctor.And || j == IBinJunctor.Or)
        ////////////////////////////////////////////////////////////////////////
        
        val (abs, newArgs) = Seqs unzip subres
        
        (abs(0).merge(abs(1), j == IBinJunctor.And), t update newArgs)
      }
    }

  }

  //////////////////////////////////////////////////////////////////////////////
  
}