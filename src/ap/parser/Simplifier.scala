/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.terfor.conjunctions.Quantifier

import IBinJunctor._
import IIntRelation._
import IExpression._
import Quantifier._
import SymbolCollector.variables

object Simplifier {

  /**
   * Simple mini-scoping, pushing down all quantifiers as far as possible
   */
  private def miniScope(expr : IExpression) : IExpression = expr match {
    case IQuantified(ALL, IBinFormula(And, f1, f2)) => all(f1) & all(f2)
    case IQuantified(EX, IBinFormula(Or, f1, f2)) => ex(f1) | ex(f2)
        
    case IQuantified(ALL, IBinFormula(Or, f1, f2))
      if (!(variables(f1) contains IVariable(0))) =>
        VariableShiftVisitor(f1, 1, -1) | all(f2)
    case IQuantified(ALL, IBinFormula(Or, f1, f2))
      if (!(variables(f2) contains IVariable(0))) =>
        all(f1) | VariableShiftVisitor(f2, 1, -1)
        
    case IQuantified(EX, IBinFormula(And, f1, f2))
      if (!(variables(f1) contains IVariable(0))) =>
        VariableShiftVisitor(f1, 1, -1) & ex(f2)
    case IQuantified(EX, IBinFormula(And, f1, f2))
      if (!(variables(f2) contains IVariable(0))) =>
        ex(f1) & VariableShiftVisitor(f2, 1, -1)
      
    case IQuantified(_, t)
      if (!(variables(t) contains IVariable(0))) =>
        VariableShiftVisitor(t, 1, -1)
          
     case _ => expr
  }
  
  /**
   * Eliminate quantifiers of the form <code>ALL _0 = t ==> ...</code> and
   * <code>EX _0 = t & ...</code>
   */
  private def elimQuantifier(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) => findDefinition(f, 0, false) match {
      case Some(t) => VariableSubstVisitor(f, (List(t), -1))
      case None => expr
    }
    case IQuantified(ALL, f) => findDefinition(f, 0, true) match {
      case Some(t) => VariableSubstVisitor(f, (List(t), -1))
      case None => expr
    }
    case _ => expr
  }
  
  private def findDefinition(f : IFormula,
                             varIndex : Int,
                             universal : Boolean) : Option[ITerm] =
    f match {
      case IQuantified(q, subF)
        if (q == (if (universal) ALL else EX)) =>
          findDefinition(subF, varIndex + 1, true)
      case IBinFormula(j, f1, f2)
        if (j == (if (universal) Or else And)) =>
          findDefinition(f1, varIndex, universal) orElse
            (findDefinition(f2, varIndex, universal))

      case INot(eq @ IIntFormula(EqZero, t)) if (universal) =>
        findDefinition(eq, varIndex, false)
        
      // TODO: generalise the following patterns
      case IIntFormula(EqZero,
                       IPlus(t, ITimes(IdealInt.MINUS_ONE, IVariable(`varIndex`))))
        if (!universal && allIndexesLargerThan(t, varIndex)) =>
          Some(VariableShiftVisitor(t, varIndex + 1, -varIndex - 1))
      case IIntFormula(EqZero,
                       IPlus(ITimes(IdealInt.MINUS_ONE, IVariable(`varIndex`)), t))
        if (!universal && allIndexesLargerThan(t, varIndex)) =>
          Some(VariableShiftVisitor(t, varIndex + 1, -varIndex - 1))
      case IIntFormula(EqZero,
                       IPlus(IVariable(`varIndex`), ITimes(IdealInt.MINUS_ONE, t)))
        if (!universal && allIndexesLargerThan(t, varIndex)) =>
          Some(VariableShiftVisitor(t, varIndex + 1, -varIndex - 1))
      case IIntFormula(EqZero,
                       IPlus(ITimes(IdealInt.MINUS_ONE, t), IVariable(`varIndex`)))
        if (!universal && allIndexesLargerThan(t, varIndex)) =>
          Some(VariableShiftVisitor(t, varIndex + 1, -varIndex - 1))
        
      case _ => None
    }
  
  private def allIndexesLargerThan(t : IExpression, limit : Int) : Boolean =
    variables(t) forall ((v) => v.index > limit)
  
  /**
   * Do some boolean simplifications, as well as elimination of trivial
   * equations and inequalities of the form <code>t - t = 0</code>,
   * <code>t - t >= 0</code>
   */
  private def elimSimpleLiterals(expr : IExpression) : IExpression = expr match {
    case IBinFormula(And, IBoolLit(true), f) => f
    case IBinFormula(And, f, IBoolLit(true)) => f
    case IBinFormula(And, IBoolLit(false), f) => false
    case IBinFormula(And, f, IBoolLit(false)) => false
    
    case IBinFormula(Or, IBoolLit(true), f) => true
    case IBinFormula(Or, f, IBoolLit(true)) => true
    case IBinFormula(Or, IBoolLit(false), f) => f
    case IBinFormula(Or, f, IBoolLit(false)) => f
    
    case INot(IBoolLit(value)) => !value
    
    // TODO: generalise
    case IPlus(IIntLit(c1), IIntLit(c2)) => c1 * c2
    case IPlus(t1, t2) if (t1 == t2) => t1 * 2
    case IPlus(t1, ITimes(c, t2)) if (t1 == t2) => t1 * (c + 1)
    case IPlus(ITimes(c, t2), t1) if (t1 == t2) => t1 * (c + 1)
    case IPlus(ITimes(c1, t1), ITimes(c2, t2)) if (t1 == t2) => t1 * (c1 + c2)
    
    case ITimes(IdealInt.ONE, t) => t
    case ITimes(IdealInt.ZERO, t) => 0
    
    case ITimes(c1, IIntLit(c2)) => c1 * c2
    case ITimes(c1, ITimes(c2, t)) => t * (c1 * c2)
    
    case IIntFormula(EqZero, IIntLit(v)) => v.isZero
    case IIntFormula(GeqZero, IIntLit(v)) => (v.signum >= 0)
      
    case _ => expr
  }
  
  /**
   * Perform various kinds of simplification to the given formula, in particular
   * mini-scoping and eliminate of simple kinds of quantifiers
   */
  def apply(expr : IFormula) : IFormula = {
    import Rewriter._
    
    val e2 = Transform2NNF(expr)
    
    val e3 =
      rewrite(e2, combineRewritings(Array(elimSimpleLiterals _,
                                          miniScope _,
                                          elimQuantifier _))).asInstanceOf[IFormula]
    
    e3
  }
  
}
