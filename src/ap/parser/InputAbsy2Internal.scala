/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap.basetypes.IdealInt
import ap.terfor.{TerFor, Formula, Term, VariableTerm, OneTerm, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, LazyConjunction}
import ap.terfor.preds.Atom
import ap.terfor.equations.EquationConj
import ap.terfor.inequalities.InEqConj
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, ArrayStack => Stack}

object InputAbsy2Internal {
  private val AC = Debug.AC_INPUT_ABSY
  
  def apply(expr : IExpression, order : TermOrder) : TerFor = expr match {
    case expr : ITerm => apply(expr, order)
    case expr : IFormula => apply(expr, order)
  }

  def apply(expr : ITerm, order : TermOrder) : Term =
    new InputAbsy2Internal(order).translateLinComb(expr)

  def apply(expr : IFormula, order : TermOrder) : Formula =
    new InputAbsy2Internal(order).translateFor(expr).toFormula
}

private class InputAbsy2Internal(order : TermOrder) {
  
  private implicit val o = order
  
  import IExpression._
  
  private val inputStack = new Stack[IExpression]
  
  /**
   * Translate an expression to the internal representation
   */
  private def translateTermCoeff(t : ITerm) : (IdealInt, Term) = t match {
    case IIntLit(v) =>
      (v, OneTerm)
    case IConstant(c) =>
      (IdealInt.ONE, c)
    case IVariable(i) =>
      (IdealInt.ONE, VariableTerm(i))
    case ITimes(c, subT) => {
      val (subC, subRes) = translateTermCoeff(subT)
      (c * subC, subRes)
    }
    
    case IPlus(t1, t2) => {
      val preInputSize = inputStack.size
      
      inputStack push t1
      inputStack push t2
      
      val subRes = new Iterator[(IdealInt, Term)] {
        def hasNext = inputStack.size > preInputSize
        def next : (IdealInt, Term) = inputStack.pop match {
          case IPlus(t1, t2) => {
            inputStack push t1
            inputStack push t2
            next
          }
          case t : ITerm =>
            translateTermCoeff(t)
        }
      }
      
      val res = LinearCombination(subRes, order)

      // ensure that no garbage remain on the stack
      while (subRes.hasNext) subRes.next

      (IdealInt.ONE, res)
    }
  }
  
  private def translateLinComb(t : ITerm) : LinearCombination = {
    val (coeff, s) = translateTermCoeff(t)
    LinearCombination(coeff, s, order)
  }
  
  private def translateFor(f : IFormula) : LazyConjunction = f match {
    case IBoolLit(true) =>
      LazyConjunction.TRUE
    case IBoolLit(false) =>
      LazyConjunction.FALSE
    case INot(subF) =>
      translateFor(subF).negate
    case IAtom(pred, args) =>
        LazyConjunction(Atom(pred,
                             for (r <- args.iterator) yield translateLinComb(r),
                             order))
    case IIntFormula(IIntRelation.EqZero, t) =>
        LazyConjunction(EquationConj(translateLinComb(t), order))
    case IIntFormula(IIntRelation.GeqZero, t) =>
        LazyConjunction(InEqConj(translateLinComb(t), order))
    case IQuantified(quan, _subF) => {
      var quans = List(quan)
      var subF = _subF
      while (subF.isInstanceOf[IQuantified]) {
        val IQuantified(quan, sf) = subF
        quans = quan :: quans
        subF = sf
      }
      
      LazyConjunction(Conjunction.quantify(quans,
                                           translateFor(subF).toConjunction,
                                           order))
    }
    case INamedPart(_, subF) =>
      // names are just ignored
      translateFor(subF)

    case IBinFormula(op, f1, f2) => {
      val preInputSize = inputStack.size

      inputStack push f1
      inputStack push f2

      var res : LazyConjunction = op match {
        case IBinJunctor.And => LazyConjunction.TRUE
        case IBinJunctor.Or =>  LazyConjunction.FALSE
      }
      
      while (inputStack.size > preInputSize) inputStack.pop match {
        case IBinFormula(`op`, f1, f2) => {
          inputStack push f1
          inputStack push f2
        }
        case f : IFormula => op match {
          case IBinJunctor.And => {
            res = res & translateFor(f)
            if (res.isFalse) {
              while (inputStack.size > preInputSize) inputStack.pop
            }
          }
          case IBinJunctor.Or => {
            res = res | translateFor(f)
            if (res.isTrue) {
              while (inputStack.size > preInputSize) inputStack.pop
            }
          }
        }
      }
      
      res
    }

/*      
    case IBinFormula(IBinJunctor.And, f1, f2) =>
      translateFor(f1) & translateFor(f2)
    case IBinFormula(IBinJunctor.Or, f1, f2) =>
      translateFor(f1) | translateFor(f2) */
  }
  
}
