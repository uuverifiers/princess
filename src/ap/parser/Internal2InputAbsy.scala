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

package ap.parser

import ap.terfor.{Term, Formula, OneTerm, VariableTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{PredConj, Atom}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.arithconj.ArithConj
import ap.util.Debug

import scala.collection.{Map => MMap}

/**
 * Converter from the internal formula datastructures to the input level AST
 * datastructures
 */
object Internal2InputAbsy {
  private val AC = Debug.AC_INPUT_ABSY
  
  import IExpression._
  
  def apply(f : Formula, predTranslation : MMap[Predicate, IFunction]) : IFormula =
    new Internal2InputAbsy(predTranslation).convert(f)

  def apply(f : Formula) : IFormula = apply(f, Map())

  def apply(t : Term, predTranslation : MMap[Predicate, IFunction]) : ITerm =
    new Internal2InputAbsy(predTranslation).convert(t)

  def apply(t : Term) : ITerm = apply(t, Map())

}

class Internal2InputAbsy(predTranslation : MMap[IExpression.Predicate, IFunction]) {
  
  import IExpression._
  
  private def convert(t : Term) : ITerm = t match {
    case OneTerm => i(1)
    case c : ConstantTerm => c
    case VariableTerm(index) => v(index)
    case lc : LinearCombination =>
      sum(for ((c, t) <- lc.pairIterator) yield {
        if (c.isOne) convert(t) else (convert(t) * c)
      })
  }

  private def convert(f : Formula) : IFormula = f match {
    case c : Conjunction => convert(c)
    case ac : ArithConj => convert(ac)
    case eqs : EquationConj => convert(eqs)
    case eqs : NegEquationConj => convert(eqs)
    case eqs : InEqConj => convert(eqs)
    case preds : PredConj => convert(preds)
  }
  
  private def convert(c : Conjunction) : IFormula =
    if (c.isFalse)
      false
    else if (c.isTrue)
      true
    else
      quan(c.quans,
           convert(c.arithConj) &&& convert(c.predConj) &&&
           connect(for (d <- c.negatedConjs.iterator) yield !convert(d),
                   IBinJunctor.And))
  
  private def convert(ac : ArithConj) : IFormula =
    convert(ac.positiveEqs) &&& convert(ac.negativeEqs) &&& convert(ac.inEqs)
  
  private def convert(eqs : EquationConj) : IFormula =
    connect(for (lc <- eqs.iterator) yield eqZero(convert(lc)), IBinJunctor.And)

  private def convert(eqs : NegEquationConj) : IFormula =
    connect(for (lc <- eqs.iterator) yield !eqZero(convert(lc)), IBinJunctor.And)
  
  private def convert(eqs : InEqConj) : IFormula =
    connect(for (lc <- eqs.iterator) yield geqZero(convert(lc)), IBinJunctor.And)
  
  private def convert(preds : PredConj) : IFormula =
    convert(preds.positiveLits, false) &&& convert(preds.negativeLits, true)
  
  private def convert(lits : Seq[Atom], negate : Boolean) : IFormula = connect(
    for (a <- lits.iterator) yield {
      val ifor = (predTranslation get a.pred) match {
        case Some(f) =>
          IFunApp(f, for (t <- a take f.arity) yield convert(t)) === convert(a.last)
        case None =>
          IAtom(a.pred, for (t <- a) yield convert(t))
      }
      if (negate) !ifor else ifor
    }, IBinJunctor.And)
  
}
