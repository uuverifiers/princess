/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010-2015 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap._
import ap.basetypes.IdealInt
import ap.parser._


/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions:
 *    \exists int a; x = store(a, b, c)
 * is replaced with
 *    select(x, b) = c 
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
      
    case IQuantified(q, subF) if (q == Quantifier(negated)) =>
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


/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions:
 *    \exists int a; x = store(a, b, c)
 * is replaced with
 *    select(x, b) = c 
 */
class InterpolantSimplifier2(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = {

    def shiftTerm(t : ITerm) : ITerm       = VariableShiftVisitor(t, depth + 1, 1)
    def shiftFor (f : IFormula) : IFormula = VariableShiftVisitor(f, depth + 1, 1)

    f match {
      case IQuantified(q, subF) if (q == Quantifier(negated)) =>
        for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
  
      case IBinFormula(j, left, right)
          if (j == (if (negated) IBinJunctor.Or else IBinJunctor.And)) =>
        (for (newLeft <- translate(left, negated, depth))
         yield IBinFormula(j, newLeft, shiftFor(right))) orElse
        (for (newRight <- translate(right, negated, depth))
         yield IBinFormula(j, shiftFor(left), newRight))
  
      case INot(f) =>
        for (res <- translate(f, !negated, depth)) yield INot(res)

      case Eq(IFunApp(`store`, Seq(w@IVariable(`depth`), t1, t2)), ar)
          if (!negated &&
              !ContainsSymbol(t1, w) && !ContainsSymbol(t2, w) &&
              !ContainsSymbol(ar, w)) =>
        Some(shiftFor(select(ar, t1) === t2) &
             (w === store(shiftTerm(ar), shiftTerm(t1), v(depth + 1))))
  
      case Eq(ar, IFunApp(`store`, Seq(w@IVariable(`depth`), t1, t2)))
          if (!negated &&
              !ContainsSymbol(t1, w) && !ContainsSymbol(t2, w) &&
              !ContainsSymbol(ar, w)) =>
        Some(shiftFor(select(ar, t1) === t2) &
             (w === store(shiftTerm(ar), shiftTerm(t1), v(depth + 1))))
  
      case _ => None
    }
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>
      (for (res <- translate(f, false, 0))
       yield { Console.err.println("" + f + " -> " + res); IQuantified(EX, IQuantified(EX, res))}) getOrElse expr
    case IQuantified(ALL, f) =>
      (for (res <- translate(f, true, 0))
       yield { Console.err.println("" + f + " -> " + res); IQuantified(ALL, IQuantified(ALL, res))}) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}
