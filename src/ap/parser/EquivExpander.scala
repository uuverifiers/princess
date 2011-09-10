/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier

/**
 * Class to turn <-> into conjunction and disjunctions, eliminate
 * if-then-else expressions and epsilon terms
 */
object EquivExpander extends ContextAwareVisitor[Unit, IExpression] {

  import IExpression._
  
  def apply(f : IFormula) : IFormula =
    this.visit(TermITETranslator.visit(f, {}), Context()).asInstanceOf[IFormula]
  
  override def preVisit(t : IExpression, c : Context[Unit]) : PreVisitResult =
    t match {
    
      case LeafFormula(t) => {
        // check whether there are any epsilon terms that we have to expand

        val searcher = new EPSSearcher
        val epsLessFor = searcher.visit(t, true).asInstanceOf[IFormula]
        
        if (searcher.foundEPS == null) {
          ShortCutResult(t)
        } else {
          
          // replace the eps constant with a fresh variable, shift all other
          // variables upwards
          val shiftedBody = new VariableShiftVisitor(0, 1) {
            override def postVisit(t : IExpression, quantifierNum : Int,
                                   subres : Seq[IExpression]) : IExpression =
              t match {
                case IConstant(c) if (c == searcher.epsConst) =>
                  v(quantifierNum)
                case t =>
                  super.postVisit(t, quantifierNum, subres)
              }
          }.visit(epsLessFor, 0).asInstanceOf[IFormula]
        
          TryAgain(if (c.polarity > 0)
                     all(searcher.foundEPS.cond ==> shiftedBody)
                   else
                     ex(searcher.foundEPS.cond & shiftedBody),
                   c)
        }
      }
      
      case IFormulaITE(cond, left, right) =>
        if ((c.binders contains Context.EX) ^ (c.polarity < 0))
          TryAgain((cond & left) | (!cond & right), c)
        else
          TryAgain((cond ==> left) & (!cond ==> right), c)
      
      case IBinFormula(IBinJunctor.Eqv, f1, f2) =>
        if ((c.binders contains Context.EX) ^ (c.polarity < 0))
          TryAgain((f1 & f2) | (!f1 & !f2), c)
        else
          TryAgain((f1 ==> f2) & (f2 ==> f1), c)
          
      case _ =>
        super.preVisit(t, c)
    }

  def postVisit(t : IExpression, c : Context[Unit],
                subres : Seq[IExpression]) : IExpression =
    t update subres

}

/**
 * Search for occurrences of ITE in the given formula. The first found
 * occurrence is stored in the field <code>foundITE</code> and replaced with a
 * fresh constant <code>iteConst</code>
 */
private class EPSSearcher extends CollectingVisitor[Boolean, IExpression] {
  
  import IExpression._
  
  var foundEPS : IEpsilon = _
  var epsConst : ConstantTerm = _
  
  override def preVisit(t : IExpression,
                        descendIntoFors : Boolean) : PreVisitResult =
    t match {
      case t if (foundEPS != null) =>
        ShortCutResult(t)
      case t : IEpsilon if (foundEPS == null) => {
        foundEPS = t
        epsConst = new ConstantTerm("eps")
        ShortCutResult(epsConst)
      }
      case t : ITerm =>
        UniSubArgs(false)
      case t : IFormula =>
        // only descend into the first level of formulae
        if (descendIntoFors) KeepArg else ShortCutResult(t)
    }
  
  def postVisit(t : IExpression,
                descendIntoFors : Boolean,
                subres : Seq[IExpression]) : IExpression =
    t update subres
  
}

/**
 * Visitor for replacing if-then-else expressions with epsilon terms
 */
private object TermITETranslator extends CollectingVisitor[Unit, IExpression] {
  import IExpression._
  
  def postVisit(t : IExpression,
                arg : Unit,
                subres : Seq[IExpression]) : IExpression = t match {
    case _ : ITermITE => {
      val cond = VariableShiftVisitor(subres(0), 0, 1).asInstanceOf[IFormula]
      val left = VariableShiftVisitor(subres(1), 0, 1).asInstanceOf[ITerm]
      val right = VariableShiftVisitor(subres(2), 0, 1).asInstanceOf[ITerm]
      eps((!cond | (v(0) === left)) & (cond | (v(0) === right)))
    }
    case t =>
      t update subres
  }
}
