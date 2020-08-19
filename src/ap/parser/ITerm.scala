/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.terfor.preds.Predicate
import ap.types.Sort
import ap.util.{Debug, Seqs}

import scala.collection.mutable.ArrayBuffer
import scala.runtime.ScalaRunTime

/**
 * Abstract class representing terms in input-syntax.
 */
abstract class ITerm extends IExpression {
  /** Sum of two terms. */
  def +(that : ITerm) : ITerm = IPlus(this, that)
  /** Product of term with an integer. */
  def *(coeff : IdealInt) : ITerm = ITimes(coeff, this)
  /**
   * Product of two terms (only defined if at least one of the terms is
   * constant).
   */
  def *(that : ITerm) : ITerm = (this, that) match {
    case (IExpression.Const(c), t) => t * c
    case (t, IExpression.Const(c)) => t * c
    case _ => throw new IllegalArgumentException(
      "Only multiplication with literal constants is defined in Presburger arithmetic.\n" +
      "Try the operator ** or the method mult instead.")
  }
  /** Negation of a term. */
  def unary_- : ITerm = ITimes(IdealInt.MINUS_ONE, this)
  /** Difference between two terms. */
  def -(that : ITerm) : ITerm = IPlus(this, -that)
  /** Equation between two terms. */
  def ===(that : ITerm) : IFormula =
//    IIntFormula(IIntRelation.EqZero, this --- that)
    IEquation(this, that)
  /** Dis-equation between two terms. */
  def =/=(that : ITerm) : IFormula =
    !(this === that)
  /** Inequality between two terms. */
  def >=(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, this --- that)
  /** Inequality between two terms. */
  def <=(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, that --- this)
  /** Inequality between two terms. */
  def >(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, this --- that +++ IIntLit(IdealInt.MINUS_ONE))
  /** Inequality between two terms. */
  def <(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, that --- this +++ IIntLit(IdealInt.MINUS_ONE))

  /**
   * Sum of two terms. The resulting expression is simplified immediately
   * if one of the terms disappears.
   */
  def +++(that : ITerm) : ITerm = (this, that) match {
    case (IExpression.Const(IdealInt.ZERO), t) => t
    case (t, IExpression.Const(IdealInt.ZERO)) => t
    case (IExpression.Const(a), IExpression.Const(b)) => IIntLit(a + b)
    case _ => this + that
  }

  /**
   * Difference of two terms. The resulting expression is simplified immediately
   * if one of the terms disappears.
   */
  def ---(that : ITerm) : ITerm = (this, that) match {
    case (IExpression.Const(a), IExpression.Const(b)) => IIntLit(a - b)
    case (IExpression.Const(IdealInt.ZERO), t) => -t
    case (t, IExpression.Const(IdealInt.ZERO)) => t
    case (t, IExpression.Const(b)) => t + IIntLit(-b)
    case _ => this - that
  }

  /** Negation of a term. The resulting expression is simplified immediately
   * if one of the terms is constant. */
  def minusSimplify : ITerm = this match {
    case IExpression.Const(a) => IIntLit(-a)
    case ITimes(coeff, t)     => ITimes(-coeff, t)
    case t                    => ITimes(IdealInt.MINUS_ONE, t)
  }

  /**
   * Product of two terms. The resulting expression is simplified immediately
   * if one of the terms is constant.
   */
  def ***(coeff : IdealInt) : ITerm = (coeff, this) match {
    case (IdealInt.ZERO, _) => IIntLit(0)
    case (IdealInt.ONE, t) => t
    case (coeff, IExpression.Const(a)) => IIntLit(coeff * a)
    case (coeff, ITimes(c, t)) => ITimes(c * coeff, t)
    case _ => this * coeff
  }

  /**
   * Replace the subexpressions of this node with new expressions
   */
  override def update(newSubExprs : Seq[IExpression]) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    this
  }
}

/**
 * Integer literals.
 */
case class IIntLit(value : IdealInt) extends ITerm {
  override def toString = value.toString
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Symbolic constants.
 */
case class IConstant(c : ConstantTerm) extends ITerm {
  override def toString = c.toString
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Bound variables of any sort.
 */
object IVariable {
  def apply(index : Int) : IVariable =
    ISortedVariable(index, Sort.Integer)
  def apply(index : Int, sort : Sort) : IVariable =
    ISortedVariable(index, sort)

  def unapply(t : IVariable) : Option[Int] = t match {
    case ISortedVariable(index, _) => Some(index)
    case _                         => None
  }
}

/**
 * Bound variables, represented using their de Bruijn index and the sort.
 */
abstract class IVariable extends ITerm {
  /**
   * The index of the bound variable.
   */
  def index : Int

  /**
   * The sort of the bound variable.
   */
  def sort : Sort

  /**
   * Increase the index of this variable by <code>shift</code> (which can
   * have any sign).
   */
  def shiftedBy(shift : Int) : IVariable
}

/**
 * Bound variables, represented using their de Bruijn index and the sort.
 */
case class ISortedVariable(index : Int, sort : Sort) extends IVariable {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, index >= 0)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * Increase the index of this variable by <code>shift</code> (which can
   * have any sign).
   */
  def shiftedBy(shift : Int) : IVariable =
    if (shift == 0) this else ISortedVariable(index + shift, sort)

  override def toString =
    "_" + index + (if (sort == Sort.Integer) "" else "[" + sort.toString + "]")
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Product between a term and an integer coefficient.
 */
case class ITimes(coeff : IdealInt, subterm : ITerm) extends ITerm {
  override def apply(i : Int) : ITerm = i match {
    case 0 => subterm
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1               
  
  override def update(newSubExprs : Seq[IExpression]) : ITimes = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[ITerm]
    if (newsub eq subterm) this else ITimes(coeff, newsub)
  }

  override def toString = "" + coeff + " * " + subterm
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Sum of two terms.
 */
case class IPlus(t1 : ITerm, t2 : ITerm) extends ITerm {
  override def apply(i : Int) : ITerm = i match {
    case 0 => t1
    case 1 => t2
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 2               

  override def update(newSubExprs : Seq[IExpression]) : IPlus = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newt1 = newSubExprs(0).asInstanceOf[ITerm]
    val newt2 = newSubExprs(1).asInstanceOf[ITerm]
    if ((newt1 eq t1) && (newt2 eq t2)) this else IPlus(newt1, newt2)
  }

  override def toString = "(" + t1 + " + " + t2 + ")"
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * An uninterpreted function with fixed arity. The function can optionally
 * be <code>partial</code> (no totality axiom) or <code>relational</code>
 * (no functionality axiom).
 */
class IFunction(val name : String, val arity : Int,
                val partial : Boolean, val relational : Boolean) {

  override def toString = name + "/" + arity +
                          (if (partial) "p" else "") +
                          (if (relational) "r" else "")

}

/**
 * Application of an uninterpreted function to a list of terms.
 */
case class IFunApp(fun : IFunction, args : Seq[ITerm]) extends ITerm {
  //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, fun.arity == args.length)
  //-END-ASSERTION-///////////////////////////////////////////////////////////  
  override def apply(i : Int) : ITerm = args(i)
  override def length : Int = args.length

  override def update(newSubExprs : Seq[IExpression]) : IFunApp =
    IExpression.toTermSeq(newSubExprs, args) match {
      case Some(newArgs) => IFunApp(fun, newArgs)
      case None => this
    }
  
  override def equals(that : Any) : Boolean = that match {
    case IFunApp(thatFun, thatArgs) =>
      (fun == thatFun) && (args sameElements thatArgs)
    case _ => false
  }
  
  override val hashCode : Int =
    fun.hashCode + Seqs.computeHashCode(args, 17, 3)

  override def toString =
    fun.name + 
    (if (args.length > 0)
       "(" + (for (t <- args.iterator) yield t.toString).mkString(", ") + ")"
     else
       "")
}

/**
 * If-then-else term.
 */
case class ITermITE(cond : IFormula, left : ITerm, right : ITerm) extends ITerm {
  override def apply(i : Int) : IExpression = i match {
    case 0 => cond
    case 1 => left
    case 2 => right
    case _ => throw new IndexOutOfBoundsException
  }
  
  override def length : Int = 3

  override def update(newSubExprs : Seq[IExpression]) : ITermITE = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 3)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newCond = newSubExprs(0).asInstanceOf[IFormula]
    val newLeft = newSubExprs(1).asInstanceOf[ITerm]
    val newRight = newSubExprs(2).asInstanceOf[ITerm]
    if ((newCond eq cond) && (newLeft eq left) && (newRight eq right))
      this
    else
      ITermITE(newCond, newLeft, newRight)
  }

  override def toString =
    "\\if (" + cond + ") \\then (" + left + ") \\else (" + right + ")"
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Epsilon term, which is defined to evaluate to an arbitrary value
 * satisfying the formula <code>cond</code>. <code>cond</code> is expected
 * to contain a bound variable with de Bruijn index 0 and any sort.
 */
object IEpsilon {
  def apply(cond : IFormula) : IEpsilon =
    ISortedEpsilon(Sort.Integer, cond)
  def apply(sort : Sort, cond : IFormula) : IEpsilon =
    ISortedEpsilon(sort, cond)

  def unapply(t : IEpsilon) : Option[IFormula] = t match {
    case ISortedEpsilon(_, cond) => Some(cond)
    case _                       => None
  }
}

/**
 * Epsilon term, which is defined to evaluate to an arbitrary value
 * satisfying the formula <code>cond</code>. <code>cond</code> is expected
 * to contain a bound variable with de Bruijn index 0 and the given sort.
 */
abstract class IEpsilon extends ITerm with IVariableBinder {
  /**
   * The sort of the bound variable.
   */
  def sort : Sort

  /**
   * The body of the epsilon term.
   */
  def cond : IFormula
}

/**
 * Epsilon term, which is defined to evaluate to an arbitrary value
 * satisfying the formula <code>cond</code>. <code>cond</code> is expected
 * to contain a bound variable with de Bruijn index 0 and the given sort.
 */
case class ISortedEpsilon(sort : Sort, cond : IFormula) extends IEpsilon {
  override def apply(i : Int) : IExpression = i match {
    case 0 => cond
    case _ => throw new IndexOutOfBoundsException
  }
  
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : ISortedEpsilon = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newCond = newSubExprs(0).asInstanceOf[IFormula]
    if (newCond eq cond) this else ISortedEpsilon(sort, newCond)
  }

  override def toString =
    "EPS " + (if (sort == Sort.Integer) "" else (sort.toString + ". ")) + cond

  override val hashCode : Int = ScalaRunTime._hashCode(this)
}
