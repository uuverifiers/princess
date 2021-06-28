/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2021 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.{Term, Formula, OneTerm, VariableTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{PredConj, Atom}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.arithconj.ArithConj
import ap.theories.Heap
import ap.types.{SortedIFunction, SortedPredicate}
import ap.util.Debug

import scala.collection.{Map => MMap}
import scala.collection.mutable.ArrayBuffer

/**
 * Converter from the internal formula datastructures to the input level AST
 * datastructures.
 */
object Internal2InputAbsy {
  private val AC = Debug.AC_INPUT_ABSY
  
  import IExpression._
  
  def apply(f : Formula,
            predTranslation : MMap[Predicate, IFunction]) : IFormula =
    (new Internal2InputAbsy(predTranslation))(f)

  def apply(f : Formula) : IFormula = apply(f, Map())

  def apply(t : Term,
            predTranslation : MMap[Predicate, IFunction]) : ITerm =
    (new Internal2InputAbsy(predTranslation))(t)

  def apply(t : Term) : ITerm = apply(t, Map())

}

class Internal2InputAbsy(
        predTranslation : MMap[IExpression.Predicate, IFunction]) {
  
  import IExpression._

  def apply(t : Term) : ITerm = convert(t)

  def apply(f : Formula) : IFormula = convert(f)

  private def convert(t : Term) : ITerm = t match {
    case OneTerm                => i(1)
    case c : ConstantTerm       => c
    case VariableTerm(index)    => v(index, Sort.AnySort)
    case lc : LinearCombination =>
      sum(for ((c, t) <- lc.pairIterator) yield {
        if (c.isOne)
          convert(t)
        else if (t == OneTerm)
          i(c)
        else
          (convert(t) * c)
      })
  }

  private def convertLC2Eq(lc : LinearCombination) : IFormula =
    if (lc.size == 2 && lc.constant.isZero &&
        lc.getCoeff(0).isOne && lc.getCoeff(1).isMinusOne)
      IEquation(convert(lc getTerm 0), convert(lc getTerm 1))
    else
      eqZero(convert(lc))

  private def convert(f : Formula) : IFormula = f match {
    case c : Conjunction       => convert(c)
    case ac : ArithConj        => convert(ac)
    case eqs : EquationConj    => convert(eqs)
    case eqs : NegEquationConj => convert(eqs)
    case eqs : InEqConj        => convert(eqs)
    case preds : PredConj      => convert(preds)
  }
  
  private def convert(c : Conjunction) : IFormula =
    quanWithSorts(
      for (q <- c.quans) yield (q, Sort.AnySort),
      convert(c.arithConj) &&& convert(c.predConj) &&&
        and(for (d <- c.negatedConjs.iterator) yield !convert(d)))
  
  private def convert(ac : ArithConj) : IFormula =
    convert(ac.positiveEqs) &&& convert(ac.negativeEqs) &&& convert(ac.inEqs)
  
  private def convert(eqs : EquationConj) : IFormula =
    if (eqs.isFalse)
      false
    else
      and(for (lc <- eqs.iterator) yield convertLC2Eq(lc))

  private def convert(eqs : NegEquationConj) : IFormula =
    if (eqs.isFalse)
      false
    else
      and(for (lc <- eqs.iterator) yield !convertLC2Eq(lc))
  
  private def convert(eqs : InEqConj) : IFormula =
    if (eqs.isFalse)
      false
    else
      and(for (lc <- eqs.iterator) yield geqZero(convert(lc)))
  
  private def convert(preds : PredConj) : IFormula =
    if (preds.isFalse)
      false
    else
      convert(preds.positiveLits, false) &&& convert(preds.negativeLits, true)
  
  private def convert(lits : Seq[Atom], negate : Boolean) : IFormula = and(
    for (a <- lits.iterator) yield {
      val ifor = (predTranslation get a.pred) match {
        case Some(f) =>
          IFunApp(f, for (t <- a take f.arity) yield convert(t)) ===
            convert(a.last)
        case None =>
          IAtom(a.pred, for (t <- a) yield convert(t))
      }
      if (negate) !ifor else ifor
    })
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor to replace quantifiers of sort <code>Any</code> with sorted
 * quantifiers, by inferring the sort of the quantified variables.
 */
object VariableSortInferenceVisitor
       extends CollectingVisitor[IExpression.Sort, IExpression] {
  import IExpression._
  import Sort.{AnySort, :::, Numeric}

  /**
   * A placeholder sort that is used in places type inference discovered
   * conflicts.
   */
  val ConflictSort = Sort.createInfUninterpretedSort("conflict")

  def apply(t : IFormula) : IFormula = {
    val t1 = infer(t)
    ConflictSortEliminator.visit(t1, ()).asInstanceOf[IFormula]
  }
  def apply(t : ITerm) : ITerm = {
    val t1 = infer(t)
    ConflictSortEliminator.visit(t1, ()).asInstanceOf[ITerm]
  }

  def infer(t : IExpression) : IExpression = {
    val res = this.visit(t, null)
    if (res eq t)
      t
    else
      infer(res)
  }

  private val variableSorts = new ArrayBuffer[Sort]

  private def getVariableSort(variableIndex : Int) : Sort =
    variableSorts(variableSorts.size - variableIndex - 1)

  private def popVariableSort : Sort = {
    val res = variableSorts.last
    variableSorts reduceToSize (variableSorts.size - 1)
    res
  }

  private def setVariableSort(variableIndex : Int, t : Sort) : Unit =
    if (t != AnySort) {
      val effectiveSort = t match {
        case Numeric(_) => Sort.Integer
        case t => t
      }

      val pos = variableSorts.size - variableIndex - 1

      variableSorts(pos) match {
        case AnySort =>
          variableSorts(pos) = effectiveSort
        case ConflictSort =>
          // nothing
        case oldSort if oldSort != effectiveSort => {
          val newSort = (oldSort, effectiveSort) match {
            case (s : Heap.AddressSort, Sort.Integer) => s
            case (Sort.Integer, s : Heap.AddressSort) => s
            case _ =>
              Debug.whenAssertionsOn(AC) {
                Console.err.println("Warning: type clash during inference: " +
                  oldSort + " vs " + t)
              }
              ConflictSort
          }
          variableSorts(pos) = newSort
        }
        case _ =>
          variableSorts(pos) = effectiveSort
      }

    }

  private def equalSorts(t1 : ITerm, t2 : ITerm) : Unit = (t1, t2) match {
    case (ISortedVariable(ind1, AnySort), t2 ::: sort2) =>
      setVariableSort(ind1, sort2)
    case (t1 ::: sort1, ISortedVariable(ind2, AnySort)) =>
      setVariableSort(ind2, sort1)
    case (ISortedVariable(ind1, Numeric(_)), t2 ::: sort2)
        if sort2.isInstanceOf[Heap.AddressSort] =>
      setVariableSort(ind1, sort2)
    case (t1 ::: sort1, ISortedVariable(ind2, Numeric(_)))
        if sort1.isInstanceOf[Heap.AddressSort] =>
      setVariableSort(ind2, sort1)
    case _ =>
      // nothing
  }

  private def intSort(t : ITerm) : Unit = t match {
    case ISortedVariable(ind, AnySort) =>
      setVariableSort(ind, Sort.Integer)
    case _ =>
      // nothing
  }

  override def preVisit(t : IExpression,
                        ctxt : Sort) : PreVisitResult = t match {
    case ISortedVariable(ind, AnySort) if ctxt != null => {
      setVariableSort(ind, ctxt)
      KeepArg
    }
    case t : IVariableBinder => {
      variableSorts += t.sort
      UniSubArgs(null)
    }
    case _ : IPlus | _ : ITimes | _ : IIntFormula =>
      UniSubArgs(Sort.Integer)
    case _ : ITermITE =>
      SubArgs(Array(null, ctxt, ctxt))
    case IFunApp(f, args) =>
      SubArgs(SortedIFunction.iArgumentSorts(f, args))
    case IAtom(p, args) =>
      SubArgs(SortedPredicate.iArgumentSorts(p, args))
    case _ =>
      UniSubArgs(null)
  }

  def postVisit(t : IExpression,
                ctxt : Sort,
                subres : Seq[IExpression]) : IExpression = t match {
    case t@ISortedVariable(ind, sort) => {
      val infSort = getVariableSort(ind)
      if (infSort != sort)
        ISortedVariable(ind, infSort)
      else
        t
    }
    case ISortedQuantified(quan, sort, body) => {
      val infSort = popVariableSort
      if (sort == infSort && (body eq subres.head))
        t
      else
        ISortedQuantified(quan, infSort, subres.head.asInstanceOf[IFormula])
    }
    case ISortedEpsilon(sort, body) => {
      val infSort = popVariableSort
      if (sort == infSort && (body eq subres.head))
        t
      else
        ISortedEpsilon(infSort, subres.head.asInstanceOf[IFormula])
    }

    case t : IEquation => {
      val res = t update subres
      equalSorts(res.left, res.right)
      res
    }
    case t : ITermITE => {
      val res = t update subres
      equalSorts(res.left, res.right)
      res
    }

    case _ =>
      t update subres
  }

  /**
   * Visitor to replace the sort
   * <code>VariableSortInferenceVisitor.ConflictSort</code> with
   * <code>Sort.AnySort</code>.
   */
  private object ConflictSortEliminator
          extends CollectingVisitor[Unit, IExpression] {

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case ISortedVariable(ind, ConflictSort) =>
        ISortedVariable(ind, AnySort)

      case ISortedQuantified(quan, ConflictSort, _) =>
        ISortedQuantified(quan, AnySort, subres(0).asInstanceOf[IFormula])
      case ISortedEpsilon(ConflictSort, _) =>
        ISortedEpsilon(AnySort, subres(0).asInstanceOf[IFormula])

      case _ =>
        t update subres
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

