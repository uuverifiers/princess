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

package ap.parser;

import ap.basetypes.IdealInt
import ap.terfor.{TerFor, Formula, Term, VariableTerm, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.equations.EquationConj
import ap.terfor.inequalities.InEqConj
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, Stack}

object InputAbsy2Internal {
  private val AC = Debug.AC_INPUT_ABSY
  
  def apply(expr : IExpression, order : TermOrder) : TerFor =
    new InputAbsy2Internal(order).visit(expr, 0).simplify(order) match {
      case r : TermResult => r.asTerm
      case r : FormulaResult => r.asFormula
    }

  def apply(expr : ITerm, order : TermOrder) : Term =
    apply(expr.asInstanceOf[IExpression], order).asInstanceOf[Term]

  def apply(expr : IFormula, order : TermOrder) : Formula =
    apply(expr.asInstanceOf[IExpression], order).asInstanceOf[Formula]
}

private class InputAbsy2Internal(order : TermOrder)
        extends CollectingVisitor[Unit, ConversionResult] {

  private def binResult(op : BinOp, subres : Seq[ConversionResult]) =
    BinResult(op,
              subres(0).simplifyIfOpChanged(op, order),
              subres(1).simplifyIfOpChanged(op, order))    
        
  def postVisit(t : IExpression, arg : Unit, subres : Seq[ConversionResult])
                                                   : ConversionResult =
    t match {
      case IIntLit(v) =>
        TermResult(LinearCombination(v))
      case IConstant(c) =>
        TermResult(c)
      case IVariable(i) =>
        TermResult(VariableTerm(i))
      case ITimes(c, _) =>
        TermResult(LinearCombination(List((c, subres(0).asTerm(order))), order))
      case _ : IPlus =>
        binResult(PlusOp, subres)
      case IBoolLit(true) =>
        FormulaResult(Conjunction.TRUE)
      case IBoolLit(false) =>
        FormulaResult(Conjunction.FALSE)
      case _ : INot =>
        FormulaResult(Conjunction.negate(subres(0).asFormula(order), order))
      case IBinFormula(IBinJunctor.And, _, _) =>
        binResult(AndOp, subres)
      case IBinFormula(IBinJunctor.Or, _, _) =>
        binResult(OrOp, subres)
      case IAtom(pred, _) =>
        FormulaResult(Atom(pred,
                           for (r <- subres.iterator)
                             yield LinearCombination(r.asTerm(order), order),
                           order))
      case IIntFormula(IIntRelation.EqZero, _) =>
        FormulaResult(EquationConj(LinearCombination(subres(0).asTerm(order), order),
                                   order))
      case IIntFormula(IIntRelation.GeqZero, _) =>
        FormulaResult(InEqConj(LinearCombination(subres(0).asTerm(order), order),
                               order))
      case IQuantified(quan, _) =>
        FormulaResult(Conjunction.quantify(List(quan), subres(0).asFormula(order),
                                           order))
      case INamedPart(_, _) =>
        // names are just ignored
        subres(0)
    }
}

////////////////////////////////////////////////////////////////////////////////
      
private abstract class ConversionResult {
  def simplify(order : TermOrder) : SimpleResult
  def asTerm(order : TermOrder) : Term = this.simplify(order).asTerm
  def asFormula(order : TermOrder) : Formula = this.simplify(order).asFormula
  def simplifyIfOpChanged(newOp : BinOp, order : TermOrder) : ConversionResult = this
}

private abstract class SimpleResult extends ConversionResult {
  def simplify(order : TermOrder) : SimpleResult = this
  def asFormula : Formula = throw new UnsupportedOperationException
  def asTerm : Term = throw new UnsupportedOperationException  
}

private case class TermResult(override val asTerm : Term) extends SimpleResult
private case class FormulaResult(override val asFormula : Formula) extends SimpleResult

private case class BinResult(op : BinOp, r1 : ConversionResult, r2 : ConversionResult)
                   extends ConversionResult with Iterable[SimpleResult] {
  def iterator = new Iterator[SimpleResult] {
    private val todo = new Stack[ConversionResult]
    todo push BinResult.this
    
    def hasNext = !todo.isEmpty
    
    def next = todo.pop match {
      case BinResult(`op`, left, right) => {
        todo push right
        todo push left
        next
      }
      case x : SimpleResult => x
    }
  }

  def simplify(order : TermOrder) : SimpleResult = op(this.iterator, order)

  override def simplifyIfOpChanged(newOp : BinOp, order : TermOrder) =
    if (op == newOp) this else simplify(order)
}

////////////////////////////////////////////////////////////////////////////////
           
private abstract class BinOp {
  def apply(els : Iterator[SimpleResult], order : TermOrder) : SimpleResult
}

private case object PlusOp extends BinOp {
  def apply(els : Iterator[SimpleResult], order : TermOrder) : SimpleResult =
    TermResult(LinearCombination(for (r <- els) yield (IdealInt.ONE, r.asTerm),
                                 order))
}

private case object AndOp extends BinOp {
  def apply(els : Iterator[SimpleResult], order : TermOrder) : SimpleResult =
    FormulaResult(Conjunction.conj(for (r <- els) yield r.asFormula, order))
}

private case object OrOp extends BinOp {
  def apply(els : Iterator[SimpleResult], order : TermOrder) : SimpleResult =
    FormulaResult(Conjunction.disj(for (r <- els) yield r.asFormula, order))
}
