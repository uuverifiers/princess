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
import ap.theories.TheoryRegistry
import ap.types.SortedConstantTerm
import ap.util.{Debug, Seqs}

import scala.collection.immutable.VectorBuilder
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

////////////////////////////////////////////////////////////////////////////////

/**
 * Common trait for <code>IExpression</code> classes that bind variables.
 * Bound variables are represented using de Bruijn indexes.
 */
trait IVariableBinder {
  /**
   * The sort of the bound variable.
   */
  def sort : ap.types.Sort
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Companion object of <code>IExpression</code>, with various helper methods.
 */
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
  /** Imported type from the <code>types</code> package */
  type Sort = ap.types.Sort
  /** Imported companion object from the <code>types</code> package */
  val Sort = ap.types.Sort
  
  /** Conversion from integers to terms */
  def i(value : Int) : ITerm = IIntLit(value)
  /** Implicit conversion from integers to terms */
  implicit def Int2ITerm(value : Int) : ITerm = IIntLit(value)

  /** Conversion from integers to terms */
  def i(value : IdealInt) : ITerm = IIntLit(value)
  /** Implicit conversion from integers to terms */
  implicit def IdealInt2ITerm(value : IdealInt) : ITerm = IIntLit(value)

  /** Conversion from constants to terms */
  def i(c : ConstantTerm) : ITerm = IConstant(c)
  /** Implicit conversion from constants to terms */
  implicit def ConstantTerm2ITerm(c : ConstantTerm) : ITerm = IConstant(c)

  /**
   * Generate the variable with de Bruijn index <code>index</code> and sort
   * <code>Sort.Integer</code>.
   */
  def v(index : Int) : IVariable = IVariable(index)

  /**
   * Generate the variable with de Bruijn index <code>index</code> and the
   * given sort.
   */
  def v(index : Int, sort : Sort) : IVariable = IVariable(index, sort)

  /** Conversion from Booleans to formulas */
  def i(value : Boolean) : IFormula = IBoolLit(value)
  /** Implicit conversion from Booleans to formulas */
  implicit def Boolean2IFormula(value : Boolean) : IFormula = IBoolLit(value)

  /** Implicit conversion from Scala ranges to interval sorts */
  implicit def Range2Interval(range : Range) : Sort.Interval = {
    if (range.step != 1)
      throw new IllegalArgumentException(
        "Only ranges with step 1 can be converted to a sort")
    val upper = if (range.isInclusive) range.end else (range.end - 1)
    if (upper < range.start)
      throw new IllegalArgumentException(
        "Sorts have to be non-empty")
    Sort.Interval(Some(range.start), Some(upper))
  }

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
   * Generate an epsilon-expression with sort <code>Sort.Integer</code>.
   */
  def eps(f : IFormula) = IEpsilon(f)

  /**
   * Generate an epsilon-expression with the given sort.
   */
  def eps(sort : Sort, f : IFormula) = IEpsilon(sort, f)

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
   * Generate a conditional term.
   */
  def ite(cond : IFormula, left : ITerm, right : ITerm) =
    ITermITE(cond, left, right)

  /**
   * Generate a conditional formula.
   */
  def ite(cond : IFormula, left : IFormula, right : IFormula) =
    IFormulaITE(cond, left, right)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an existential quantifier for the variable with de Bruijn index 0.
   */
  def ex(f : IFormula) = IQuantified(Quantifier.EX, f)
  
  /**
   * Add an existential quantifier for the variable with de Bruijn index 0.
   */
  def all(f : IFormula) = IQuantified(Quantifier.ALL, f)
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>ex(a => phi(a))</code>.
   */
  def ex(f : ITerm => IFormula) = quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>ex((a, b) => phi(a, b))</code>.
   */
  def ex(f : (ITerm, ITerm) => IFormula) = quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>ex((a, b, c) => phi(a, b, c))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm) => IFormula) = quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>ex((a, b, c, d) => phi(a, b, c, d))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm, ITerm) => IFormula) = quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as
   * <code>ex((a, b, c, d, e) => phi(a, b, c, d, e))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm, ITerm, ITerm) => IFormula) =
    quan(Quantifier.EX, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>all(a => phi(a))</code>.
   */
  def all(f : ITerm => IFormula) = quan(Quantifier.ALL, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>all((a, b) => phi(a, b))</code>.
   */
  def all(f : (ITerm, ITerm) => IFormula) = quan(Quantifier.ALL, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>all((a, b, c) => phi(a, b, c))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm) => IFormula) = quan(Quantifier.ALL, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>all((a, b, c, d) => phi(a, b, c, d))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm, ITerm) => IFormula) =
    quan(Quantifier.ALL, f)
  
  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as
   * <code>all((a, b, c, d, e) => phi(a, b, c, d, e))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm, ITerm, ITerm) => IFormula) =
    quan(Quantifier.ALL, f)
  
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
   * Higher-order syntax for quantifiers. This makes it possible
   * to write a quantifier like in
   * <code>quan(Quantifier.ALL, (a, b) => phi(a, b))</code>.
   */
  def quan(q : Quantifier, f : (ITerm, ITerm) => IFormula) : IFormula = {
    val x1 = new ConstantTerm ("x1")
    val x2 = new ConstantTerm ("x2")
    quanConsts(q, List(x1, x2), f(x1, x2))
  }
  
  /**
   * Higher-order syntax for quantifiers. This makes it possible
   * to write a quantifier like in
   * <code>quan(Quantifier.ALL, (a, b, c) => phi(a, b, c))</code>.
   */
  def quan(q : Quantifier,
           f : (ITerm, ITerm, ITerm) => IFormula) : IFormula = {
    val x1 = new ConstantTerm ("x1")
    val x2 = new ConstantTerm ("x2")
    val x3 = new ConstantTerm ("x3")
    quanConsts(q, List(x1, x2, x3), f(x1, x2, x3))
  }
  
  /**
   * Higher-order syntax for quantifiers. This makes it possible
   * to write a quantifier like in
   * <code>quan(Quantifier.ALL, (a, b, c, d) => phi(a, b, c, d))</code>.
   */
  def quan(q : Quantifier,
           f : (ITerm, ITerm, ITerm, ITerm) => IFormula) : IFormula = {
    val x1 = new ConstantTerm ("x1")
    val x2 = new ConstantTerm ("x2")
    val x3 = new ConstantTerm ("x3")
    val x4 = new ConstantTerm ("x4")
    quanConsts(q, List(x1, x2, x3, x4), f(x1, x2, x3, x4))
  }
  
  /**
   * Higher-order syntax for quantifiers. This makes it possible
   * to write a quantifier like in
   * <code>quan(Quantifier.ALL, (a, b, c, d, e) => phi(a, b, c, d, e))</code>.
   */
  def quan(q : Quantifier,
           f : (ITerm, ITerm, ITerm, ITerm, ITerm) => IFormula) : IFormula = {
    val x1 = new ConstantTerm ("x1")
    val x2 = new ConstantTerm ("x2")
    val x3 = new ConstantTerm ("x3")
    val x4 = new ConstantTerm ("x4")
    val x5 = new ConstantTerm ("x5")
    quanConsts(q, List(x1, x2, x3, x4, x5), f(x1, x2, x3, x4, x5))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add quantifiers for the variables with de Bruijn index
   * <code>0, ..., quans.size - 1</code>. The first quantifier in
   * <code>quans</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def quan(quans : Seq[Quantifier], f : IFormula) : IFormula =
    (f /: quans)((f, q) => IQuantified(q, f))

  /**
   * Add quantifiers for the variables with de Bruijn index
   * <code>0, ..., sorts.size - 1</code>. The first sort in
   * <code>sorts</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def quanWithSorts(q : Quantifier, sorts : Seq[Sort],
                    f : IFormula) : IFormula =
    (f /: sorts)((f, s) => ISortedQuantified(q, s, f))

  /**
   * Add quantifiers for the variables with de Bruijn index
   * <code>0, ..., quans.size - 1</code>. The first quantifier in
   * <code>quans</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def quanWithSorts(quans : Seq[(Quantifier, Sort)], f : IFormula) : IFormula =
    (f /: quans) { case (f, (q, sort)) => ISortedQuantified(q, sort, f) }

  /**
   * Quantify some of the variables occurring in a formula.
   */
  def quanVars(quan : Quantifier, vars : Iterable[IVariable],
               f : IFormula) : IFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, vars.toSet.size == vars.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (vars.isEmpty) {
      f
    } else {
      // First need to reorder the variables
      val shifts =
        (for ((IVariable(v), n) <- vars.iterator.zipWithIndex)
         yield (v, n - v)).toMap
      val shiftedF =
        VariablePermVisitor(f, IVarShift(shifts, vars.size))

      // then add quantifiers
      (vars :\ shiftedF) {
        case (ISortedVariable(_, sort), g) => ISortedQuantified(quan, sort, g)
      }
    }
  }

  /**
   * Replace <code>consts</code> with bound variables, and quantify them.
   */
  def quanConsts(quan : Quantifier,
                 consts : Iterable[ConstantTerm],
                 f : IFormula) : IFormula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, consts.toSet.size == consts.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val constsSeq = consts.toSeq
    val sorts = constsSeq map (SortedConstantTerm sortOf _)

    val fWithShiftedVars = VariableShiftVisitor(f, 0, consts.size)
    val subst = (for (((c, s), i) <-
                      (constsSeq.iterator zip sorts.iterator).zipWithIndex)
                 yield (c, v(i, s))).toMap
    val fWithSubstitutedConsts = ConstantSubstVisitor(fWithShiftedVars, subst)

    quan match {
      case Quantifier.ALL => all(sorts, fWithSubstitutedConsts)
      case Quantifier.EX  => ex (sorts, fWithSubstitutedConsts)
    }
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
      case ((Quantifier.ALL, c), f) => (SortedConstantTerm sortOf c) all f
      case ((Quantifier.EX,  c), f) => (SortedConstantTerm sortOf c) ex f
    }
  }

  /**
   * Trigger/patterns that are used to define in which way a quantified 
   * formula is supposed to be instantiated. Triggers are only allowed to occur
   * immediately after (inside) a quantifier. This class can both represent
   * uni-triggers (for <code>patterns.size == 1</code> and multi-triggers.
   * Intended use is, for instance,
   * <code>all(x => trig(f(x) >= 0, f(x)))</code>.
   */
  def trig(f : IFormula, patterns : IExpression*) =
    ITrigger(ITrigger.extractTerms(patterns), f)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Guard a formula, turning it into <code>f & guard</code>. The guard will
   * be inserted underneath leading existential quantifiers.
   */
  def guardEx(f : IFormula, guard : IFormula) : IFormula = guard match {
    case IBoolLit(true) => f
    case guard          => guardEx(f, guard, 0)
  }

  private def guardEx(f : IFormula, guard : IFormula,
                      depth : Int) : IFormula = f match {
    case IQuantified(Quantifier.EX, body) =>
      IQuantified(Quantifier.EX, guardEx(body, guard, depth + 1))
    case ITrigger(patterns, body) =>
      ITrigger(patterns, guardEx(body, guard, depth))
    case f =>
      VariableShiftVisitor(guard, 0, depth) & f
  }

  /**
   * Guard a formula, turning it into <code>f ==> guard</code>. The guard will
   * be inserted underneath leading universal quantifiers.
   */
  def guardAll(f : IFormula, guard : IFormula) : IFormula = guard match {
    case IBoolLit(true) => f
    case guard          => guardAll(f, guard, 0)
  }

  private def guardAll(f : IFormula, guard : IFormula,
                       depth : Int) : IFormula = f match {
    case IQuantified(Quantifier.ALL, body) =>
      IQuantified(Quantifier.ALL, guardAll(body, guard, depth + 1))
    case ITrigger(patterns, body) =>
      ITrigger(patterns, guardAll(body, guard, depth))
    case f =>
      VariableShiftVisitor(guard, 0, depth) ==> f
  }

  /**
   * Add sorted universal quantifiers for the variables with de Bruijn index
   * <code>0, ..., sorts.size - 1</code>. The first sort in
   * <code>sorts</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def all(sorts : Seq[Sort], f : IFormula) : IFormula =
    quanWithSorts(for (s <- sorts) yield (Quantifier.ALL, s), f)

  /**
   * Add sorted existential quantifiers for the variables with de Bruijn index
   * <code>0, ..., sorts.size - 1</code>. The first sort in
   * <code>sorts</code> will be the innermost quantifier and corresponds
   * to index 0. 
   */
  def ex(sorts : Seq[Sort], f : IFormula) : IFormula =
    quanWithSorts(for (s <- sorts) yield (Quantifier.EX, s), f)

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * When encoding functions using predicates, make sure that
   * no functions escape.
   */
  def containFunctionApplications(f : IFormula) : IFormula =
    all(ITrigger(List(0), VariableShiftVisitor(f, 0, 1)))

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
   * Shift all variables with <code>index >= offset</code> by
   * <code>shift</code>.
   */
  def shiftVars(t : IExpression, offset : Int, shift : Int) =
    VariableShiftVisitor(t, offset, shift)

  /**
   * Shift all variables by <code>shift</code>.
   */
  def shiftVars(t : IExpression, shift : Int) =
    VariableShiftVisitor(t, 0, shift)

  /**
   * Shift all variables with <code>index >= offset</code> by
   * <code>shift</code>.
   */
  def shiftVars(t : IFormula, offset : Int, shift : Int) =
    VariableShiftVisitor(t, offset, shift)

  /**
   * Shift all variables by <code>shift</code>.
   */
  def shiftVars(t : IFormula, shift : Int) =
    VariableShiftVisitor(t, 0, shift)

  /**
   * Shift all variables with <code>index >= offset</code> by
   * <code>shift</code>.
   */
  def shiftVars(t : ITerm, offset : Int, shift : Int) =
    VariableShiftVisitor(t, offset, shift)

  /**
   * Shift all variables by <code>shift</code>.
   */
  def shiftVars(t : ITerm, shift : Int) =
    VariableShiftVisitor(t, 0, shift)

  //////////////////////////////////////////////////////////////////////////////

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
      case IEquation(t, IIntLit(IdealInt.ZERO)) => Some(t)
      case IEquation(IIntLit(IdealInt.ZERO), t) => Some(t)
      case IIntFormula(IIntRelation.EqZero, t)  => Some(t)
      case _ => None
    }
  }
  
  /**
   * Generate or match an equation <code>s === t</code>.
   */
  object Eq {
    def apply(s : ITerm, t : ITerm) : IFormula = (s === t)
    def unapply(f : IFormula) : Option[(ITerm, ITerm)] = f match {
      case IEquation(s, t) =>
        Some((s, t))
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
   * Generate or match an equation <code>s === lit</code>,
   * where <code>lit</code> is an integer literal.
   */
  object EqLit {
    def apply(s : ITerm, t : IdealInt) : IFormula = (s === t)
    def unapply(f : IFormula) : Option[(ITerm, IdealInt)] = f match {
      case IEquation(a, IIntLit(c)) =>
        Some((a, c))
      case IEquation(IIntLit(c), a) =>
        Some((a, c))
      case IIntFormula(IIntRelation.EqZero,
                       IPlus(ITimes(IdealInt.MINUS_ONE, a), IIntLit(c))) =>
        Some((a, c))
      case IIntFormula(IIntRelation.EqZero,
                       IPlus(IIntLit(c), ITimes(IdealInt.MINUS_ONE, a))) =>
        Some((a, c))
      case IIntFormula(IIntRelation.EqZero, IPlus(a, IIntLit(c))) =>
        Some((a, -c))
      case IIntFormula(IIntRelation.EqZero, IPlus(IIntLit(c), a)) =>
        Some((a, -c))
      case IIntFormula(IIntRelation.EqZero, t) =>
        Some((t, IdealInt.ZERO))
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

  def connectSimplify(fors : Iterable[IFormula],
                      op : IBinJunctor.Value) : IFormula =
    connectSimplify(fors.iterator, op)

  def connectSimplify(fors : Iterator[IFormula],
                      op : IBinJunctor.Value) : IFormula =
    if (fors.hasNext) op match {
      case IBinJunctor.And => fors reduceLeft (_ &&& _)
      case IBinJunctor.Or  => fors reduceLeft (_ ||| _)
      case IBinJunctor.Eqv => fors reduceLeft (_ <===> _)
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

  /** Identify terms that only consist of variables, constants,
      and linear arithmetic operations. */
  object SimpleTerm {
    def unapply(t : ITerm) : Option[ITerm] =
      if (isSimpleTerm(t)) Some(t) else None
  }
  
  /** Identify terms that only consist of variables, constants,
      and linear arithmetic operations. */
  def isSimpleTerm(t : ITerm) : Boolean = t match {
    case IPlus(t1, t2) =>
      isSimpleTerm(t1) && isSimpleTerm(t2)
    case ITimes(_, t1) =>
      isSimpleTerm(t1)
    case _ : IConstant | _ : IVariable | _ : IIntLit =>
      true
    case _ =>
      false
  }

  /** Identify formulae that do not have direct subformulae. */
  object LeafFormula {
    def unapply(t : IExpression) : Option[IFormula] = t match {
      case t : IBoolLit    => Some(t)
      case t : IAtom       => Some(t)
      case t : IIntFormula => Some(t)
      case t : IEquation   => Some(t)
      case _               => None
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
   * Rewrite an equation to the form <code>coeff * symbol = remainder</code>
   * (where remainder does not contain the atomic term
   * <code>symbol</code>) and determine the coefficient and the remainder
   */
  case class SymbolEquation(symbol : ITerm) {
    private val SSum = SymbolSum(symbol)

    def unapply(f : IFormula) : Option[(IdealInt, ITerm)] = f match {
      case IIntFormula(IIntRelation.EqZero, SSum(coeff, rem)) =>
        Some((-coeff, rem))
      case IEquation(left, right) => (left - right) match {
        case SSum(coeff, rem) => Some((-coeff, rem))
        case _                => None
      }
      case _ =>
        None
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

      case IPlus(ITimes(aCoeff, a),
                 ITimes(bCoeff, b)) =>
        (aCoeff.signum, bCoeff.signum) match {
          case (1, 1) | (_, -1)                    => Some((ITimes(aCoeff, a),
                                                            ITimes(-bCoeff, b)))
          case (-1, 1)                             => Some((ITimes(bCoeff, b),
                                                            ITimes(-aCoeff, a)))
          case _                                   => None
        }
      case IPlus(a, ITimes(bCoeff, b))             => Some((a, ITimes(-bCoeff, b)))
      case IPlus(ITimes(aCoeff, a), b)             => Some((b, ITimes(-aCoeff, a)))

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
  
    /** Disequation of vectors (vectors differ in at least one component) */
    def =/=(that : Seq[ITerm]) =
      or(for (t <- that.iterator) yield (term =/= t))

    /** Component-wise disequation of vectors
     * (all components of the vector are different from a term) */
    def =/=/=(that : Seq[ITerm]) =
      and(for (t <- that.iterator) yield (term =/= t))
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

    /** Negated equation between two vectors */
    def =/=(that : Seq[ITerm]) =
      or(for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 =/= t2))
    /** Negated equation a vector and a term */
    def =/=(that : ITerm) =
      or(for (t <- terms.iterator) yield (t =/= that))

    /** Component-wise disequation of vectors
     * (all components of the vectors are different) */
    def =/=/=(that : Seq[ITerm]) =
      and(for ((t1, t2) <- terms.iterator zip that.iterator) yield (t1 =/= t2))
    /** Component-wise disequation of vectors
     * (all components of the vectors are different) */
    def =/=/=(that : ITerm) =
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
      val newArgs = new VectorBuilder[ITerm]
      var changed = false

      val newEIt = newExprs.iterator
      val oldEIt = oldExprs.iterator
      while (newEIt.hasNext) {
        val newArg = newEIt.next.asInstanceOf[ITerm]
        if (!(newArg eq oldEIt.next)) changed = true
        newArgs += newArg
      }
      if (changed) Some(newArgs.result) else None
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
    case t : IEquation => newSubExpr match {
      case Seq(IIntLit(c), IIntLit(d))                 => IBoolLit(c == d)
      case Seq(s : IConstant, t : IConstant) if s == t => IBoolLit(true)
      case Seq(s : IVariable, t : IVariable) if s == t => IBoolLit(true)
      case _                                           => t update newSubExpr
    }

    case t@IIntFormula(IIntRelation.EqZero, _) => newSubExpr match {
      case Seq(IIntLit(value)) =>
        IBoolLit(value.isZero)
      case Seq(ITermITE(cond, IIntLit(value1), t2)) if (!value1.isZero) =>
        ~cond &&& updateAndSimplify(t, List(t2))
      case Seq(ITermITE(cond, t1, IIntLit(value2))) if (!value2.isZero) =>
        cond &&& updateAndSimplify(t, List(t1))
      case _ =>
        t update newSubExpr
    }
    
    case t@IIntFormula(IIntRelation.GeqZero, _) => newSubExpr match {
      case Seq(IIntLit(value)) => IBoolLit(value.signum >= 0)
      case _                   => t update newSubExpr
    }
    
    case t@INot(_) => newSubExpr match {
      case Seq(IBoolLit(value)) => IBoolLit(!value)
      case Seq(INot(f))         => f
      case _                    => t update newSubExpr
    }

    case t@IBinFormula(IBinJunctor.And, _, _) => newSubExpr match {
      case Seq(s@IBoolLit(false), _)         => s
      case Seq(_, s@IBoolLit(false))         => s
      case Seq(IBoolLit(true), s : IFormula) => s
      case Seq(s : IFormula, IBoolLit(true)) => s
      case _                                 => t update newSubExpr
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
      case Seq(IBoolLit(true), left : IFormula, _)        => left
      case Seq(IBoolLit(false), _, right : IFormula)      => right
      case Seq(_, s@IBoolLit(a), IBoolLit(b)) if (a == b) => s
      case _                                              => t update newSubExpr
    }
    
    case _ : IQuantified | _ : ITrigger => newSubExpr match {
      case Seq(b : IBoolLit) => b
      case _                 => t update newSubExpr
    }

    case t@IAtom(p, _) => {
      val newAtom = t update newSubExpr
      (for (theory <- TheoryRegistry lookupSymbol p;
            res <- theory evalPred newAtom)
       yield IBoolLit(res)) getOrElse newAtom
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

    case t@IFunApp(f, _) => {
      val newApp = t update newSubExpr
      (for (theory <- TheoryRegistry lookupSymbol f;
            res <- theory evalFun newApp) yield res) getOrElse newApp
    }
    
    case t =>
      t update newSubExpr
  }
}
