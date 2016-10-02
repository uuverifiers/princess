/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.util.{Debug, Seqs}

import scala.collection.mutable.ArrayBuffer
import scala.runtime.ScalaRunTime

/**
 * Abstract syntax for prover input. The language represented by the following
 * constructors is more general than the logic that the prover actually can
 * handle (e.g., there are also functions, equivalence, etc.). The idea is
 * that inputs first have to be normalised in some way so that the prover can
 * handle them.
 */
abstract class IExpression {
  /**
   * Return the <code>i</code>th sub-expression.
   */
  def apply(i : Int) : IExpression = throw new IndexOutOfBoundsException

  /**
   * Number of sub-expressions.
   */
  def length : Int = 0
  
  /**
   * Iterator over the sub-expressions of this expression.
   */
  def iterator : Iterator[IExpression] =
    for (i <- (0 until length).iterator) yield apply(i)
  
  /**
   * Replace the subexpressions of this node with new expressions
   */
  def update(newSubExprs : Seq[IExpression]) : IExpression = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    this
  }

  /**
   * The sub-expressions of this expression.
   */
  def subExpressions = new IndexedSeq[IExpression] {
    def apply(i : Int) : IExpression = IExpression.this.apply(i)
    def length : Int = IExpression.this.length
    override def iterator = IExpression.this.iterator
  }
}

object IExpression {
  protected[parser] val AC = Debug.AC_INPUT_ABSY

  /** Imported type from the <code>terfor</code> package */
  type ConstantTerm = ap.terfor.ConstantTerm
  /** Imported type from the <code>terfor</code> package */
  type Quantifier = ap.terfor.conjunctions.Quantifier
  /** Imported companion object from the <code>terfor</code> package */
  val Quantifier = ap.terfor.conjunctions.Quantifier
  /** Imported type from the <code>terfor</code> package */
  type Predicate = ap.terfor.preds.Predicate
  
  /** Implicit conversion from integers to terms */
  def i(value : Int) : ITerm = IIntLit(value)
  /** Implicit conversion from integers to terms */
  implicit def Int2ITerm(value : Int) : ITerm = IIntLit(value)

  /** Implicit conversion from integers to terms */
  def i(value : IdealInt) : ITerm = IIntLit(value)
  /** Implicit conversion from integers to terms */
  implicit def IdealInt2ITerm(value : IdealInt) : ITerm = IIntLit(value)

  /** Implicit conversion from constants to terms */
  def i(c : ConstantTerm) : ITerm = IConstant(c)
  /** Implicit conversion from constants to terms */
  implicit def ConstantTerm2ITerm(c : ConstantTerm) : ITerm = IConstant(c)

  /**
   * Generate the variable with de Bruijn index <code>index</code>
   */
  def v(index : Int) : IVariable = IVariable(index)

  /** Implicit conversion from Booleans to formulas */
  def i(value : Boolean) : IFormula = IBoolLit(value)
  /** Implicit conversion from Booleans to formulas */
  implicit def Boolean2IFormula(value : Boolean) : IFormula = IBoolLit(value)

  /**
   * Implicit conversion, to enable the application of a predicate
   * to a sequence of terms, like in <code>p(s, t)</code>.
   */
  implicit def toPredApplier(pred : Predicate) = new PredApplier(pred)

  /**
   * Class implementing prefix-notation for predicates
   */
  class PredApplier(pred : Predicate) {
    def apply(args : ITerm*) = IAtom(pred, args)
  }
  
  /**
   * Implicit conversion, to enable the application of a function
   * to a sequence of terms, like in <code>f(s, t)</code>.
   */
  implicit def toFunApplier(fun : IFunction) = new FunApplier(fun)

  /**
   * Class implementing prefix-notation for functions
   */
  class FunApplier(fun : IFunction) {
    def apply(args : ITerm*) = IFunApp(fun, args)
  }

  /**
   * Class implementing prefix-notation for functions that are
   * considered Boolean-valued. Booleans are encoded into integers,
   * mapping <code>true</code> to <code>0</code> and <code>false</code>
   * to <code>1</code>.
   */
  class BooleanFunApplier(val fun : IFunction) {
    def apply(args : ITerm*) = eqZero(IFunApp(fun, args))
  }

  /**
   * Add an existential quantifier for the variable with de Bruijn index 0.
   */
  def ex(f : IFormula) = IQuantified(Quantifier.EX, f)
  
  /**
   * Add an existential quantifier for the variable with de Bruijn index 0.
   */
  def all(f : IFormula) = IQuantified(Quantifier.ALL, f)
  
  /**
   * Generate an epsilon-expression.
   */
  def eps(f : IFormula) = IEpsilon(f)

  /**
   * Generate a conditional term.
   */
  def ite(cond : IFormula, left : ITerm, right : ITerm) =
    ITermITE(cond, left, right)

  /**
   * Generate a conditional formula.
   */
  def ite(cond : IFormula, left : IFormula, right : IFormula) =
    IFormulaITE(cond, left, right)

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>ex(a => phi(a))</code>.
   */
  def ex(f : ITerm => IFormula) = quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>all(a => phi(a))</code>.
   */
  def all(f : ITerm => IFormula) = quan(Quantifier.ALL, f)
  
  /**
   * Higher-order syntax for quantifiers. This makes it possible
   * to write a quantifier like in
   * <code>quan(Quantifier.ALL, a => phi(a))</code>.
   */
  def quan(q : Quantifier, f : ITerm => IFormula) : IFormula = {
    // first substitute a fresh constant, and later replace it with a
    // bound variable (just applying <code>f</code> to a bound variable
    // would not work in case of nested binders)
    val x = new ConstantTerm ("x")
    quanConsts(q, List(x), f(x))
  }
  
  /**
   * Higher-order syntax for epsilon-expressions. This makes it possible
   * to write things like <code>eps(a => phi(a))</code>.
   */
  def eps(f : ITerm => IFormula) = {
    // first substitute a fresh constant, and later replace it with a
    // bound variable (just applying <code>f</code> to a bound variable
    // would not work in case of nested binders)
    val x = new ConstantTerm ("x")
    val fWithShiftedVars = VariableShiftVisitor(f(x), 0, 1)
    IEpsilon(ConstantSubstVisitor(fWithShiftedVars, Map(x -> v(0))))
  }

  /**
   * Trigger/patterns that are used to define in which way a quantified 
   * formula is supposed to be instantiated. Triggers are only allowed to occur
   * immediately after (inside) a quantifier. This class can both represent
   * uni-triggers (for <code>patterns.size == 1</code> and multi-triggers.
   * Intended use is, for instance, <code>all(x => trig(f(x) >= 0, f(x)))</code>.
   */
  def trig(f : IFormula, patterns : IExpression*) =
    ITrigger(ITrigger.extractTerms(patterns), f)
  
  /**
   * Add quantifiers for the variables with de Bruijn index
   * <code>0, ..., quans.size - 1</code>. The first quantifier in
   * <code>quans</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def quan(quans : Seq[Quantifier], f : IFormula) : IFormula =
    (f /: quans)((f, q) => IQuantified(q, f))

  /**
   * Replace <code>consts</code> with bound variables, and quantify them.
   */
  def quanConsts(quan : Quantifier,
                 consts : Iterable[ConstantTerm],
                 f : IFormula) : IFormula = {
    val fWithShiftedVars = VariableShiftVisitor(f, 0, consts.size)
    val subst = (for ((c, i) <- consts.iterator.zipWithIndex)
                 yield (c, v(i))).toMap
    val fWithSubstitutedConsts = ConstantSubstVisitor(fWithShiftedVars, subst)
    (consts :\ fWithSubstitutedConsts) ((c, f) => IQuantified(quan, f))
  }
  
  /**
   * Replace the constants in <code>quantifiedConstants</code>
   * with bound variables, and quantify them.
   */
  def quanConsts(quantifiedConstants : Seq[(Quantifier, ConstantTerm)],
                 f : IFormula) : IFormula = {
    val fWithShiftedVars = VariableShiftVisitor(f, 0, quantifiedConstants.size)
    val subst = (for (((_, c), i) <- quantifiedConstants.iterator.zipWithIndex)
                 yield (c, v(quantifiedConstants.size - i - 1))).toMap
    val fWithSubstitutedConsts = ConstantSubstVisitor(fWithShiftedVars, subst)
    (quantifiedConstants :\ fWithSubstitutedConsts) {
      case ((q, _), f) => IQuantified(q, f)
    }
  }
  
  /**
   * Substitute terms for the variables with de Bruijn index
   * <code>0, ..., replacement.size - 1</code>, and increment all other
   * variables by <code>shift</code>. 
   */
  def subst(t : ITerm, replacement : List[ITerm], shift : Int) =
    VariableSubstVisitor(t, (replacement, shift))
    
  /**
   * Substitute terms for the variables with de Bruijn index
   * <code>0, ..., replacement.size - 1</code>, and increment all other
   * variables by <code>shift</code>. 
   */
  def subst(t : IFormula, replacement : List[ITerm], shift : Int) =
    VariableSubstVisitor(t, (replacement, shift))

  /**
   * Substitute terms for the variables with de Bruijn index
   * <code>0, ..., replacement.size - 1</code>, and increment all other
   * variables by <code>shift</code>. 
   */
  def subst(t : IExpression, replacement : List[ITerm], shift : Int) =
    VariableSubstVisitor(t, (replacement, shift))

  /**
   * Generate the equation <code>t = 0</code>.
   */
  def eqZero(t : ITerm) : IFormula = IIntFormula(IIntRelation.EqZero, t)

  /**
   * Generate or match the equation <code>t = 0</code>.
   */
  object EqZ {
    def apply(t : ITerm) : IFormula = IIntFormula(IIntRelation.EqZero, t)
    def unapply(f : IFormula) : Option[ITerm] = f match {
      case IIntFormula(IIntRelation.EqZero, t) => Some(t)
      case _ => None
    }
  }
  
  /**
   * Generate or match an equation <code>s === t</code>.
   */
  object Eq {
    def apply(s : ITerm, t : ITerm) : IFormula = (s === t)
    def unapply(f : IFormula) : Option[(ITerm, ITerm)] = f match {
      case IIntFormula(IIntRelation.EqZero, Difference(s, t)) =>
        Some((s, t))
      case IIntFormula(IIntRelation.EqZero, ITimes(IdealInt.MINUS_ONE, t)) =>
        Some((i(0), t))
      case IIntFormula(IIntRelation.EqZero, t) =>
        Some((t, i(0)))
      case _ =>
        None
    }
  }
  
  /**
   * Generate the inequality <code>t >= 0</code>.
   */
  def geqZero(t : ITerm) : IFormula = IIntFormula(IIntRelation.GeqZero, t)
  
  /**
   * Generate or match the inequality <code>t >= 0</code>.
   */
  object GeqZ {
    def apply(t : ITerm) : IFormula = IIntFormula(IIntRelation.GeqZero, t)
    def unapply(f : IFormula) : Option[ITerm] = f match {
      case IIntFormula(IIntRelation.GeqZero, t) => Some(t)
      case _ => None
    }
  }

  /**
   * Generate or match an inequality <code>s >= t</code>.
   */
  object Geq {
    def apply(s : ITerm, t : ITerm) : IFormula = (s >= t)
    def unapply(f : IFormula) : Option[(ITerm, ITerm)] = f match {
      case IIntFormula(IIntRelation.GeqZero, Difference(s, t)) =>
        Some((s, t))
      case IIntFormula(IIntRelation.GeqZero, ITimes(IdealInt.MINUS_ONE, t)) =>
        Some((i(0), t))
      case IIntFormula(IIntRelation.GeqZero, t) =>
        Some((t, i(0)))
      case _ =>
        None
    }
  }

  def connect(fors : Iterable[IFormula], op : IBinJunctor.Value) : IFormula =
    connect(fors.iterator, op)

  def connect(fors : Iterator[IFormula], op : IBinJunctor.Value) : IFormula =
    if (fors.hasNext) {
      fors reduceLeft (IBinFormula(op, _, _))
    } else op match {
      case IBinJunctor.And | IBinJunctor.Eqv => true
      case IBinJunctor.Or => false
    }

  /**
   * Generate the conjunction of the given formulas.
   */
  def and(fors : Iterator[IFormula]) = connect(fors, IBinJunctor.And)
  /**
   * Generate the conjunction of the given formulas.
   */
  def and(fors : Iterable[IFormula]) = connect(fors, IBinJunctor.And)
  /**
   * Generate the disjunction of the given formulas.
   */
  def or(fors : Iterator[IFormula]) = connect(fors, IBinJunctor.Or)
  /**
   * Generate the disjunction of the given formulas.
   */
  def or(fors : Iterable[IFormula]) = connect(fors, IBinJunctor.Or)
  
  /**
   * Generate or match a binary conjunction <code>phi & psi</code>.
   */
  object Conj {
    def apply(a : IFormula, b : IFormula) = a & b
    def unapply(f : IFormula) : Option[(IFormula, IFormula)] = f match {
      case IBinFormula(IBinJunctor.And, a, b) => Some((a, b))
      case _ => None
    }
  }

  /**
   * Generate or match a binary disjunction <code>phi | psi</code>.
   */
  object Disj {
    def apply(a : IFormula, b : IFormula) = a | b
    def unapply(f : IFormula) : Option[(IFormula, IFormula)] = f match {
      case IBinFormula(IBinJunctor.Or, a, b) => Some((a, b))
      case _ => None
    }
  }

  /**
   * Generate the sum of the given terms.
   */
  def sum(terms : Iterable[ITerm]) : ITerm = sum(terms.iterator)

  /**
   * Generate the sum of the given terms.
   */
  def sum(terms : Iterator[ITerm]) : ITerm =
    if (terms.hasNext) terms reduceLeft (IPlus(_, _)) else i(0)

  /**
   * Generate a formula expressing that the given terms are
   * pairwise distinct
   */
  def distinct(terms : Iterator[ITerm]) : IFormula = {
    var termList = terms.toList
    var res : IFormula = true

    while (!termList.isEmpty) {
      val t1 = termList.head
      termList = termList.tail
      for (t2 <- termList.iterator)
        res = res &&& (t1 =/= t2)
    }

    res
  }

  /**
   * Generate a formula expressing that the given terms are
   * pairwise distinct
   */
  def distinct(terms : Iterable[ITerm]) : IFormula =
    distinct(terms.iterator)

  /**
   * Absolute value
   */
  def abs(t : ITerm) : ITerm = t match {
    case Const(tVal) => tVal.abs
    case t           => ite(geqZero(t), t, -t)
  }

  /**
   * Maximum value of a sequence of terms
   */
  def max(terms : Iterable[ITerm]) : ITerm = {
    val shTerms =
      (for (t <- terms.iterator) yield VariableShiftVisitor(t, 0, 1)).toList
    eps(or( for (t <- shTerms.iterator) yield (v(0) === t)) &
        and(for (t <- shTerms.iterator) yield (v(0) >= t)))
  }

  /**
   * Minimum value of a sequence of terms
   */
  def min(terms : Iterable[ITerm]) : ITerm = {
    val shTerms =
      (for (t <- terms.iterator) yield VariableShiftVisitor(t, 0, 1)).toList
    eps(or( for (t <- shTerms.iterator) yield (v(0) === t)) &
        and(for (t <- shTerms.iterator) yield (v(0) <= t)))
  }
  
  /** Extract the value of constant terms. */
  object Const {
    def unapply(t : ITerm) : Option[IdealInt] = t match {
      case IIntLit(v) => Some(v)
      case ITimes(IdealInt.ZERO, _) => Some(IdealInt.ZERO)
      case ITimes(c, Const(v)) => Some(c * v)
      case IPlus(Const(v1), Const(v2)) => Some(v1 + v2)
      case _ => None
    }
  }

  /** Extract the value and sign of constant terms. */
  object SignConst {
    def unapply(t : ITerm) : Option[(IdealInt, Int)] = t match {
      case Const(v) => Some((v, v.signum))
      case _ => None
    }
  }
  
  /** Identify formulae that do not have direct subformulae. */
  object LeafFormula {
    def unapply(t : IExpression) : Option[IFormula] = t match {
      case t : IBoolLit => Some(t)
      case t : IAtom => Some(t)
      case t : IIntFormula => Some(t)
      case _ => None
    }
  }
  
  /**
   * Rewrite a term to the form <code>coeff * symbol + remainder</code>
   * (where remainder does not contain the atomic term
   * <code>symbol</code>) and determine the coefficient and the remainder
   */
  case class SymbolSum(symbol : ITerm) {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC, symbol.isInstanceOf[IVariable] ||
                         symbol.isInstanceOf[IConstant])
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    def unapply(t : ITerm) : Option[(IdealInt, ITerm)] ={
      val (coeff, remainder) = decompose(t, 1)
      symbol match {
        case _ : IVariable | _ : IConstant
          if (ContainsSymbol(remainder, symbol)) => None
        case _ => Some(coeff, remainder)
      }
    }

    private def decompose(t : ITerm,
                          coeff : IdealInt) : (IdealInt, ITerm) = t match {
      case `symbol` => (coeff, 0)
      case ITimes(c, t) => decompose(t, coeff * c)
      case IPlus(a, b) => {
        val (ca, ra) = decompose(a, coeff)
        val (cb, rb) = decompose(b, coeff)
        (ca + cb, ra +++ rb)
      }
      case _ => (0, t *** coeff)
    }
  }

  /**
   * Match on a difference
   * <code>IPlus(a, ITimes(IdealInt.MINUS_ONE, b))</code>
   * or
   * <code>IPlus(ITimes(IdealInt.MINUS_ONE, b), a)</code>
   */
  object Difference {
    def unapply(t : ITerm) : Option[(ITerm, ITerm)] = t match {
      case IPlus(ITimes(IdealInt.ONE, a),
                 ITimes(IdealInt.MINUS_ONE, b))    => Some((a, b))
      case IPlus(ITimes(IdealInt.MINUS_ONE, b),
                 ITimes(IdealInt.ONE, a))          => Some((a, b))
      case IPlus(a, ITimes(IdealInt.MINUS_ONE, b)) => Some((a, b))
      case IPlus(ITimes(IdealInt.MINUS_ONE, b), a) => Some((a, b))
      case IPlus(a, IIntLit(value))                => Some((a, IIntLit(-value)))
      case IPlus(IIntLit(value), a)                => Some((a, IIntLit(-value)))
      case _                                       => None
    }
  }

  // Classes to talk about sequences of terms in a more succinct way
  
  implicit def iterm2RichITerm(lc : ITerm) : RichITerm =
    new RichITerm(lc)
  
  implicit def itermSeq2RichITermSeq(lcs : Seq[ITerm]) : RichITermSeq =
    new RichITermSeq(lcs)

  implicit def constantSeq2RichITermSeq(lcs : Seq[ConstantTerm]) : RichITermSeq =
    new RichITermSeq(lcs map (IConstant(_)))

  implicit def constantSeq2ITermSeq(lcs : Seq[ConstantTerm]) : Seq[ITerm] =
    lcs map (IConstant(_))

  class RichITerm(term : ITerm) {
    // various component-wise operations
    def +++(that : Seq[ITerm]) : Seq[ITerm] = for (t <- that) yield (term + t)
    def ---(that : Seq[ITerm]) : Seq[ITerm] = for (t <- that) yield (term - t)
  
    // component-wise disequation on vectors
    def =/=(that : Seq[ITerm]) = and(for (t <- that.iterator) yield (term =/= t))
  }

  /**
   * Various functions to work with vectors of terms
   */
  class RichITermSeq(terms : Seq[ITerm]) {
    /** Component-wise addition */
    def +++(that : Seq[ITerm]) : Seq[ITerm] =
      (for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 + t2)).toList
    /** Component-wise addition */
    def +++(that : ITerm) : Seq[ITerm] =
      for (t <- terms) yield (t + that)
    /** Component-wise subtraction */
    def ---(that : Seq[ITerm]) : Seq[ITerm] =
      (for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 --- t2)).toList
    /** Component-wise subtraction */
    def ---(that : ITerm) : Seq[ITerm] =
      for (t <- terms) yield (t --- that)
    /** Component-wise multiplication */
    def ***(that : Seq[ITerm]) : Seq[ITerm] =
      (for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 * t2)).toList
    /** Component-wise multiplication */
    def ***(that : ITerm) : Seq[ITerm] =
      for (t <- terms) yield (t * that)
  
    /** The dot-product of two vectors */
    def *:*(that : Seq[ITerm]) : ITerm =
      sum(for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 * t2))

    def unary_- : Seq[ITerm] = for (t <- terms) yield -t
    def ===(that : Seq[ITerm]) = and((this --- that) map (eqZero(_)))
    def ===(that : ITerm) = and((this --- that) map (eqZero(_)))
    def >=(that : Seq[ITerm]) = and((this --- that) map (geqZero(_)))
    def >=(that : ITerm) = and((this --- that) map (geqZero(_)))
    def >(that : Seq[ITerm]) = and((this --- that --- 1) map (geqZero(_)))
    def >(that : ITerm) = and((this --- that --- 1) map (geqZero(_)))
    def <=(that : Seq[ITerm]) = and((that --- terms) map (geqZero(_)))
    def <=(that : ITerm) = and((that --- terms) map (geqZero(_)))
    def <(that : Seq[ITerm]) = and((that --- terms --- 1) map (geqZero(_)))
    def <(that : ITerm) = and((that --- terms --- 1) map (geqZero(_)))

    // component-wise disequation on vectors
    def =/=(that : Seq[ITerm]) =
      and(for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 =/= t2))
    def =/=(that : ITerm) =
      and(for (t <- terms.iterator) yield (t =/= that))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  protected[parser] def toTermSeq(newExprs : Seq[IExpression],
                                  oldExprs : Seq[ITerm]) : Option[Seq[ITerm]] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newExprs.length == oldExprs.length)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (oldExprs.length == 0) {
      None
    } else {
      val newArgs = new scala.collection.mutable.ArrayBuffer[ITerm]
      var changed = false

      val newEIt = newExprs.iterator
      val oldEIt = oldExprs.iterator
      while (newEIt.hasNext) {
        val newArg = newEIt.next.asInstanceOf[ITerm]
        if (!(newArg eq oldEIt.next)) changed = true
        newArgs += newArg
      }
      if (changed) Some(newArgs) else None
    }
  }
  
  def removePartName(t : IFormula) : IFormula = t match {
    case INamedPart(_, subFor) => subFor
    case _ => t
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update sub-expressions; if the expression changed as a result of the
   * update, check whether simplifications are possible.
   */
  def updateAndSimplifyLazily(e : IExpression,
                              newSubExpr : Seq[IExpression]) : IExpression = {
    val newE = e update newSubExpr
    if (newE eq e) {
      e
    } else {
      updateAndSimplify(e, newSubExpr)
    }
  }

  /**
   * Update sub-expressions; if the expression changed as a result of the
   * update, check whether simplifications are possible.
   */
  def updateAndSimplifyLazily(e : IFormula,
                              newSubExpr : Seq[IExpression]) : IFormula = {
    val newE = e update newSubExpr
    if (newE eq e) {
      e
    } else {
      updateAndSimplify(e, newSubExpr)
    }
  }

  /**
   * Update sub-expressions; if the expression changed as a result of the
   * update, check whether simplifications are possible.
   */
  def updateAndSimplifyLazily(e : ITerm,
                              newSubExpr : Seq[IExpression]) : ITerm = {
    val newE = e update newSubExpr
    if (newE eq e) {
      e
    } else {
      updateAndSimplify(e, newSubExpr)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update sub-expressions, and directly check whether simplifications
   * are possible.
   */
  def updateAndSimplify(e : IExpression,
                        newSubExpr : Seq[IExpression]) : IExpression = e match {
    case e : IFormula => updateAndSimplify(e, newSubExpr)
    case e : ITerm =>    updateAndSimplify(e, newSubExpr)
  }
  
  /**
   * Update sub-expressions, and directly check whether simplifications
   * are possible.
   */
  def updateAndSimplify(t : IFormula,
                        newSubExpr : Seq[IExpression]) : IFormula = t match {
        case t@IIntFormula(IIntRelation.EqZero, _) => newSubExpr match {
          case Seq(IIntLit(value)) => IBoolLit(value.isZero)
          case Seq(ITermITE(cond, IIntLit(value1), t2)) if (!value1.isZero) =>
            ~cond &&& updateAndSimplify(t, List(t2))
          case Seq(ITermITE(cond, t1, IIntLit(value2))) if (!value2.isZero) =>
            cond &&& updateAndSimplify(t, List(t1))
          case _ => t update newSubExpr
        }
        
        case t@IIntFormula(IIntRelation.GeqZero, _) => newSubExpr match {
          case Seq(IIntLit(value)) => IBoolLit(value.signum >= 0)
          case _ => t update newSubExpr
        }
        
        case t@INot(_) => newSubExpr match {
          case Seq(IBoolLit(value)) => IBoolLit(!value)
          case Seq(INot(f)) => f
          case _ => t update newSubExpr
        }

        case t@IBinFormula(IBinJunctor.And, _, _) => newSubExpr match {
          case Seq(s@IBoolLit(false), _)         => s
          case Seq(_, s@IBoolLit(false))         => s
          case Seq(IBoolLit(true), s : IFormula) => s
          case Seq(s : IFormula, IBoolLit(true)) => s
          case _ => t update newSubExpr
        }
        
        case t@IBinFormula(IBinJunctor.Or, _, _) => newSubExpr match {
          case Seq(IBoolLit(false), s : IFormula) => s
          case Seq(s : IFormula, IBoolLit(false)) => s
          case Seq(s@IBoolLit(true), _)           => s
          case Seq(_, s@IBoolLit(true))           => s
          case _ => t update newSubExpr
        }
        
        case t@IBinFormula(IBinJunctor.Eqv, _, _) => newSubExpr match {
          case Seq(IBoolLit(true), s : IFormula)  => s
          case Seq(s : IFormula, IBoolLit(true))  => s
          case Seq(IBoolLit(false), s : IFormula) => ~s
          case Seq(s : IFormula, IBoolLit(false)) => ~s
          case _ => t update newSubExpr
        }
        
        case t : IFormulaITE => newSubExpr match {
          case Seq(IBoolLit(true), left : IFormula, _) => left
          case Seq(IBoolLit(false), _, right : IFormula) => right
          case Seq(_, s@IBoolLit(a), IBoolLit(b)) if (a == b) => s
          case _ => t update newSubExpr
        }
        
        case _ : IQuantified | _ : ITrigger => newSubExpr match {
          case Seq(b : IBoolLit) => b
          case _ => t update newSubExpr
        }

        case t =>
          t update newSubExpr
  }
  
  /**
   * Update sub-expressions, and directly check whether simplifications
   * are possible.
   */
  def updateAndSimplify(e : ITerm,
                        newSubExpr : Seq[IExpression]) : ITerm = e match {
        case t@ITimes(coeff, _) => newSubExpr(0) match {
          case IIntLit(value) => IIntLit(coeff * value)
          case ITimes(coeff2, s) => ITimes(coeff * coeff2, s)
          case _ => t update newSubExpr
        }
        
        case t@IPlus(_, _) => newSubExpr match {
          case Seq(t : ITerm, IIntLit(IdealInt.ZERO)) => t
          case Seq(IIntLit(IdealInt.ZERO), t : ITerm) => t
          case Seq(IIntLit(value1), IIntLit(value2)) => IIntLit(value1 + value2)
          case Seq(s : IConstant, ITimes(IdealInt.MINUS_ONE, t : IConstant))
            if (s == t) => IIntLit(IdealInt.ZERO)
          case Seq(ITimes(IdealInt.MINUS_ONE, t : IConstant), s : IConstant)
            if (s == t) => IIntLit(IdealInt.ZERO)
          case Seq(s : IVariable, ITimes(IdealInt.MINUS_ONE, t : IVariable))
            if (s == t) => IIntLit(IdealInt.ZERO)
          case Seq(ITimes(IdealInt.MINUS_ONE, t : IVariable), s : IVariable)
            if (s == t) => IIntLit(IdealInt.ZERO)
          case _ => t update newSubExpr
        }
    
        case t : ITermITE => newSubExpr match {
          case Seq(IBoolLit(true), left : ITerm, _) => left
          case Seq(IBoolLit(false), _, right : ITerm) => right
          case Seq(_, left : ITerm, right : ITerm)
            if ((left.isInstanceOf[IIntLit] ||
                 left.isInstanceOf[IConstant] ||
                 left.isInstanceOf[IVariable]) &&
                left == right) => left
          case _ => t update newSubExpr
        }
        
        case t =>
          t update newSubExpr
  }
}

//////////////////////////////////////////////////////////////////////////////

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
    IIntFormula(IIntRelation.EqZero, this --- that)
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
    case (IExpression.Const(IdealInt.ZERO), t) => -t
    case (t, IExpression.Const(IdealInt.ZERO)) => t
    case (IExpression.Const(a), IExpression.Const(b)) => IIntLit(a - b)
    case _ => this - that
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
 * Bound variables, represented using their de Bruijn index.
 */
case class IVariable(index : Int) extends ITerm {
  //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, index >= 0)
  //-END-ASSERTION-///////////////////////////////////////////////////////////
  override def toString = "_" + index
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
 * to contain a bound variable with de Bruijn index 0.
 */
case class IEpsilon(cond : IFormula) extends ITerm {
  override def apply(i : Int) : IExpression = i match {
    case 0 => cond
    case _ => throw new IndexOutOfBoundsException
  }
  
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : IEpsilon = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newCond = newSubExprs(0).asInstanceOf[IFormula]
    if (newCond eq cond) this else IEpsilon(newCond)
  }

  override def toString = "EPS " + cond
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}


//////////////////////////////////////////////////////////////////////////////

/**
 * Abstract class representing formulae in input-syntax.
 */
abstract class IFormula extends IExpression {
  /** Conjunction of two formulas. */
  def &(that : IFormula) : IFormula = IBinFormula(IBinJunctor.And, this, that)
  /** Disjunction of two formulas. */
  def |(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Or, this, that)
  /** Equivalence of two formulas. */
  def <=>(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Eqv, this, that)
  /** Exclusive-or of two formulas. */
  def </>(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Eqv, !this, that)
  /** Implication between two formulas. */
  def ==>(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Or, !this, that)
  /** Negation of a formula. */
  def unary_! : IFormula = INot(this)  

  /** Negation of a formula, with direct simplification. */
  def unary_~ : IFormula = this match {
    case INot(f) => f
    case IBoolLit(value) => IBoolLit(!value)
    case _ => !this
  }

  /** Negation of a formula, with direct simplification. */
  def notSimplify = ~this

  /**
   * Conjunction operator that directly simplify expressions involving true/false.
   */
  def &&&(that : IFormula) : IFormula = (this, that) match {
    case (f@IBoolLit(false), _) => f
    case (_, f@IBoolLit(false)) => f
    case (IBoolLit(true), f) => f
    case (f, IBoolLit(true)) => f
    case _ => this & that
  }
    
  /**
   * Conjunction operator that directly simplify expressions involving true/false.
   */
  def andSimplify(that : IFormula) = this &&& that

  /**
   * Disjunction operator that directly simplify expressions involving true/false.
   */
  def |||(that : IFormula) : IFormula = (this, that) match {
    case (f@IBoolLit(true), _) => f
    case (_, f@IBoolLit(true)) => f
    case (IBoolLit(false), f) => f
    case (f, IBoolLit(false)) => f
    case _ => this | that
  }

  /**
   * Disjunction operator that directly simplify expressions involving true/false.
   */
  def orSimplify(that : IFormula) = this ||| that
  
  /**
   * Implication operator that directly simplify expressions involving true/false.
   */
  def ===>(that : IFormula) : IFormula = (this, that) match {
    case (IBoolLit(false), _) => true
    case (_, f@IBoolLit(true)) => f
    case (IBoolLit(true), f) => f
    case (f, IBoolLit(false)) => !f
    case _ => this ==> that
  }

  /**
   * Disjunction operator that directly simplify expressions involving true/false.
   */
  def impSimplify(that : IFormula) = this ===> that
  
  /**
   * Equivalence operator that directly simplify expressions involving true/false.
   */
  def <===>(that : IFormula) : IFormula = (this, that) match {
    case (IBoolLit(true), s)  => s
    case (s, IBoolLit(true))  => s
    case (IBoolLit(false), s) => ~s
    case (s, IBoolLit(false)) => ~s
    case _ => this <=> that
  }

  /**
   * Equivalence operator that directly simplify expressions involving true/false.
   */
  def eqvSimplify(that : IFormula) = this <===> that

  /**
   * Incomplete check whether the given formula is valid.
   */
  def isTrue : Boolean = this match {
    case IBoolLit(true) => true
    case _ => false
  }

  /**
   * Incomplete check whether the given formula is unsatisfiable.
   */
  def isFalse : Boolean = this match {
    case IBoolLit(false) => true
    case _ => false
  }

  /**
   * Replace the subexpressions of this node with new expressions
   */
  override def update(newSubExprs : Seq[IExpression]) : IFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    this
  }
}

/**
 * Boolean literal.
 */
case class IBoolLit(value : Boolean) extends IFormula {
  override def toString = value.toString
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Negation of a formula.
 */
case class INot(subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : INot = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else INot(newsub)
  }
  
  override def toString = "!" + subformula
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Binary Boolean connectives.
 */
object IBinJunctor extends Enumeration {
  val And, Or, Eqv = Value
}

/**
 * Boolean combination of two formulae.
 */
case class IBinFormula(j : IBinJunctor.Value,
                       f1 : IFormula, f2 : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => f1
    case 1 => f2
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 2

  override def update(newSubExprs : Seq[IExpression]) : IBinFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newf1 = newSubExprs(0).asInstanceOf[IFormula]
    val newf2 = newSubExprs(1).asInstanceOf[IFormula]
    if ((newf1 eq f1) && (newf2 eq f2))
      this
    else
      IBinFormula(j, newf1, newf2)
  }

  override def toString = {
    import IBinJunctor._
    val sym = j match {
      case And => " & "
      case Or => " | "
      case Eqv => " <-> "
    }
    "(" + f1 + sym + f2 + ")"
  }
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Application of an uninterpreted predicate to a list of terms.
 */
case class IAtom(pred : Predicate, args : Seq[ITerm]) extends IFormula {
  //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, pred.arity == args.length)
  //-END-ASSERTION-///////////////////////////////////////////////////////////  
  override def apply(i : Int) : ITerm = args(i)
  override def length : Int = args.length

  override def update(newSubExprs : Seq[IExpression]) : IAtom =
    IExpression.toTermSeq(newSubExprs, args) match {
      case Some(newArgs) => IAtom(pred, newArgs)
      case None => this
    }
  
  override def equals(that : Any) : Boolean = that match {
    case IAtom(thatPred, thatArgs) =>
      (pred == thatPred) && (args sameElements thatArgs)
    case _ => false
  }
  
  override val hashCode : Int =
    pred.hashCode + Seqs.computeHashCode(args, 17, 3)
  
  override def toString =
    pred.name + 
    (if (args.length > 0)
       "(" + (for (t <- args.iterator) yield t.toString).mkString(", ") + ")"
     else
       "")

}

/**
 * Integer relation operators.
 */
object IIntRelation extends Enumeration {
  val EqZero, GeqZero = Value
}

/**
 * Equation or inequality.
 */
case class IIntFormula(rel : IIntRelation.Value, t : ITerm) extends IFormula {
  override def apply(i : Int) : ITerm = i match {
    case 0 => t
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : IIntFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newt = newSubExprs(0).asInstanceOf[ITerm]
    if (newt eq t) this else IIntFormula(rel, newt)
  }

  override def toString = {
    import IIntRelation._
    val sym = rel match {
      case EqZero => " = 0"
      case GeqZero => " >= 0"
    }
    "(" + t + sym + ")"
  }
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Application of a quantifier to a formula containing a free variable
 * with de Bruijn index 0.
 */
case class IQuantified(quan : Quantifier, subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : IQuantified = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else IQuantified(quan, newsub)
  }

  override def toString = "" + quan + " " + subformula
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * If-then-else formula.
 */
case class IFormulaITE(cond : IFormula,
                       left : IFormula, right : IFormula) extends IFormula {
  override def apply(i : Int) : IExpression = i match {
    case 0 => cond
    case 1 => left
    case 2 => right
    case _ => throw new IndexOutOfBoundsException
  }
  
  override def length : Int = 3

  override def update(newSubExprs : Seq[IExpression]) : IFormulaITE = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 3)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newCond = newSubExprs(0).asInstanceOf[IFormula]
    val newLeft = newSubExprs(1).asInstanceOf[IFormula]
    val newRight = newSubExprs(2).asInstanceOf[IFormula]
    if ((newCond eq cond) && (newLeft eq left) && (newRight eq right))
      this
    else
      IFormulaITE(newCond, newLeft, newRight)
  }

  override def toString =
    "\\if (" + cond + ") \\then (" + left + ") \\else (" + right + ")"
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

object ITrigger {
  /**
   * Extract terms from a set of arbitrary expressions that can
   * be used as triggers.
   */
  def extractTerms(rawPatterns : Seq[IExpression]) : Seq[ITerm] = {
    val patterns = new ArrayBuffer[ITerm]
    val extractor = new CollectingVisitor[Unit, Boolean] {
      override def preVisit(t : IExpression,
                            arg : Unit) : PreVisitResult = t match {
        case _ : IQuantified | _ : IEpsilon => ShortCutResult(false)
        case _ => KeepArg
      }
      def postVisit(t : IExpression, arg : Unit,
                    subres : Seq[Boolean]) : Boolean = t match {
        case _ : IConstant | _ : IVariable | _ : IIntLit =>
          true
        case _ : IFunApp | _ : ITimes | _ : IPlus
            if (!(subres contains false)) =>
          true
        case _ => {
          for ((s : ITerm, true) <- t.iterator zip subres.iterator)
            patterns += s
          false
        }
      }
    }

    for (p <- rawPatterns)
      if (extractor.visit(p, ()))
        patterns += p.asInstanceOf[ITerm]
    patterns.toList
  }
}

/**
 * Trigger/patterns that are used to define in which way a quantified 
 * formula is supposed to be instantiated. Triggers are only allowed to occur
 * immediately after (inside) a quantifier. This class can both represent
 * uni-triggers (for <code>patterns.size == 1</code> and multi-triggers.
 */
case class ITrigger(patterns : Seq[ITerm], subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IExpression = 
    if (i == patterns.length) subformula else patterns(i)
  override def length : Int = patterns.length + 1

  override def update(newSubExprs : Seq[IExpression]) : ITrigger = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newSubformula = newSubExprs.last.asInstanceOf[IFormula]
    IExpression.toTermSeq(newSubExprs take (newSubExprs.length - 1),
                          patterns) match {
      case Some(newPatterns) =>
        ITrigger(newPatterns, newSubformula)
      case None =>
        if (subformula eq newSubformula)
          this
        else
          ITrigger(patterns, newSubformula)
    }
  }

  override def toString = "{" + patterns.mkString(", ") + " } " + subformula
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

////////////////////////////////////////////////////////////////////////////////

object PartName {
  /** The distinguished name used for unnamed formula parts. */
  val NO_NAME = new PartName ("NoName")
}

/**
 * Formula label, used to give names to different partitions used for
 * interpolation.
 */
class PartName(override val toString : String)

/**
 * A labelled formula with name <code>name</code>.
 */
case class INamedPart(name : PartName, subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1
  
  override def update(newSubExprs : Seq[IExpression]) : INamedPart = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else INamedPart(name, newsub)
  }

  override def toString = "\\part[" + name + "] " + subformula 
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Specification of an interpolation problem, consisting of two lists
 * of formula names.
 */
case class IInterpolantSpec(left : List[PartName], right : List[PartName]) {
  override val hashCode : Int = ScalaRunTime._hashCode(this)
}
