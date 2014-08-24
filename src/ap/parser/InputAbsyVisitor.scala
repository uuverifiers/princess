/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import IExpression.{ConstantTerm, Predicate}
import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Logic, PlainRange, Seqs}

import scala.collection.mutable.{ArrayStack => Stack, ArrayBuffer,
                                 LinkedHashSet, HashSet => MHashSet}
import scala.collection.{Map => CMap}


object CollectingVisitor {
  private val AC = Debug.AC_INPUT_ABSY
}


/**
 * Visitor schema that traverses an expression in depth-first left-first order.
 * For each node, the method <code>preVisit</code> is called when descending
 * and the method <code>postVisit</code> when returning. The visitor works
 * with iteration (not recursion) and is able to deal also with large
 * expressions
 */
abstract class CollectingVisitor[A, R] {

  abstract class PreVisitResult  

  /**
   * Use the same argument for the direct sub-expressions as for this expression
   */
  case object KeepArg extends PreVisitResult
  
  /**
   * Call <code>preVisit</code> again with a different expression and argument
   */
  case class TryAgain(newT : IExpression, newArg : A) extends PreVisitResult
  
  /**
   * Use <code>arg</code> for each of the direct sub-expressions
   */
  case class UniSubArgs(arg : A) extends PreVisitResult
  
  /**
   * Specify the arguments to use for the individual sub-expressions
   */
  case class SubArgs(args : Seq[A]) extends PreVisitResult
  
  /**
   * Skip the call to <code>postVisit</code> and do not visit any of the
   * sub-expressions. Instead, directly return <code>res</code> as result
   */
  case class ShortCutResult(res : R) extends PreVisitResult
  
  def preVisit(t : IExpression, arg : A) : PreVisitResult = KeepArg
  def postVisit(t : IExpression, arg : A, subres : Seq[R]) : R
  
  def visit(expr : IExpression, arg : A) : R = {
    val toVisit = new Stack[IExpression]
    val argsToVisit = new Stack[A]
    val results = new Stack[R]

    val subRes = new ArrayBuffer[R]
    object subResReverseView extends Seq[R] {
      var N : Int = 0
      def length = N
      def apply(n : Int) = subRes(N - n - 1)
      def iterator = new Iterator[R] {
        var n = N - 1
        def hasNext = n >= 0
        def next = {
          val res = subRes(n)
          n = n - 1
          res
        }
      }
    }

    toVisit push expr
    argsToVisit push arg
    
    while (!toVisit.isEmpty) toVisit.pop match {
      case PostVisit(expr, arg) => {
        subResReverseView.N = expr.length

        var i = subResReverseView.N - 1
        while (i >= 0) {
          subRes += results.pop
          i = i - 1
        }

        results push postVisit(expr, arg, subResReverseView)
        subRes.clear
      }
      
      case expr => {
        val arg = argsToVisit.pop

        preVisit(expr, arg) match {
          case ShortCutResult(res) =>
            // directly push the result, skip the call to postVisit and the
            // recursive calls
            results push res
          
          case TryAgain(newT, newArg) => {
            toVisit push newT
            argsToVisit push newArg
          }
            
          case argModifier => 
            if (expr.length > 0) {
              // recurse
          
              toVisit push PostVisit(expr, arg)
              for (i <- (expr.length - 1) to 0 by -1) toVisit push expr(i)
        
              argModifier match {
                case KeepArg =>
                  for (_ <- PlainRange(expr.length)) argsToVisit push arg
                case UniSubArgs(subArg) =>
                  for (_ <- PlainRange(expr.length)) argsToVisit push subArg
                case SubArgs(subArgs) => {
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(CollectingVisitor.AC, subArgs.length == expr.length)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  for (i <- (expr.length - 1) to 0 by -1) argsToVisit push subArgs(i)
                }
              }
          
            } else {
              // otherwise, we can directly call the postVisit method
          
              results push postVisit(expr, arg, List())
            }
        }
      }
    }
          
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(CollectingVisitor.AC, results.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    results.pop
  }
  
  def visitWithoutResult(expr : IExpression, arg : A) : Unit = {
    val toVisit = new Stack[IExpression]
    val argsToVisit = new Stack[A]
    
    toVisit push expr
    argsToVisit push arg
    
    while (!toVisit.isEmpty) toVisit.pop match {
      case PostVisit(expr, arg) =>
        postVisit(expr, arg, null)
      
      case expr => {
        val arg = argsToVisit.pop

        preVisit(expr, arg) match {
          case ShortCutResult(res) => {
            // directly push the result, skip the call to postVisit and the
            // recursive calls
          }
          
          case TryAgain(newT, newArg) => {
            toVisit push newT
            argsToVisit push newArg
          }
            
          case argModifier => 
            if (expr.length > 0) {
              // recurse
          
              toVisit push PostVisit(expr, arg)
              for (i <- (expr.length - 1) to 0 by -1) toVisit push expr(i)
        
              argModifier match {
                case KeepArg =>
                  for (_ <- PlainRange(expr.length)) argsToVisit push arg
                case UniSubArgs(subArg) =>
                  for (_ <- PlainRange(expr.length)) argsToVisit push subArg
                case SubArgs(subArgs) => {
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(CollectingVisitor.AC, subArgs.length == expr.length)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  for (i <- (expr.length - 1) to 0 by -1) argsToVisit push subArgs(i)
                }
              }
          
            } else {
              // otherwise, we can directly call the postVisit method
          
              postVisit(expr, arg, List())
            }
        }
      }
    }
  }
  
  private case class PostVisit(expr : IExpression, arg : A)
                     extends IExpression
  
}

////////////////////////////////////////////////////////////////////////////////

object VariableShiftVisitor {
  private val AC = Debug.AC_INPUT_ABSY
  
  def apply(t : IExpression, offset : Int, shift : Int) : IExpression =
    if (shift == 0)
      t
    else
      new VariableShiftVisitor(offset, shift).visit(t, 0)
  
  def apply(t : IFormula, offset : Int, shift : Int) : IFormula =
    apply(t.asInstanceOf[IExpression], offset, shift).asInstanceOf[IFormula]
  def apply(t : ITerm, offset : Int, shift : Int) : ITerm =
    apply(t.asInstanceOf[IExpression], offset, shift).asInstanceOf[ITerm]
}

class VariableShiftVisitor(offset : Int, shift : Int)
      extends CollectingVisitor[Int, IExpression] {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(VariableShiftVisitor.AC, offset >= 0 && offset + shift >= 0)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////     

  override def preVisit(t : IExpression, quantifierNum : Int) : PreVisitResult =
    t match {
      case _ : IQuantified | _ : IEpsilon => UniSubArgs(quantifierNum + 1)
      case _ => KeepArg
    }
  def postVisit(t : IExpression, quantifierNum : Int,
                subres : Seq[IExpression]) : IExpression =
    t match {
      case IVariable(i) =>
        if (i < offset + quantifierNum) t else IVariable(i + shift)
      case _ =>
        t update subres
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * More general visitor for renaming variables. The argument of the visitor
 * methods is a pair <code>(List[Int], Int)</code> that describes how each
 * variable should be shifted: <code>(List(0, 2, -1), 1)</code> specifies that
 * variable 0 stays the same, variable 1 is increased by 2 (renamed to 3),
 * variable 2 is renamed to 1, and all other variables n are renamed to n+1.
 */
object VariablePermVisitor extends CollectingVisitor[IVarShift, IExpression] {

  def apply(t : IExpression, shifts : IVarShift) : IExpression =
    if (shifts.isIdentity) t else this.visit(t, shifts)

  def apply(t : IFormula, shifts : IVarShift) : IFormula =
    apply(t.asInstanceOf[IExpression], shifts).asInstanceOf[IFormula]
  def apply(t : ITerm, shifts : IVarShift) : ITerm =
    apply(t.asInstanceOf[IExpression], shifts).asInstanceOf[ITerm]

  override def preVisit(t : IExpression, shifts : IVarShift) : PreVisitResult =
    t match {
      case _ : IQuantified | _ : IEpsilon => UniSubArgs(shifts push 0)
      case _ => KeepArg
    }

  def postVisit(t : IExpression, shifts : IVarShift,
                subres : Seq[IExpression]) : IExpression =
    t match {
      case t : IVariable => shifts(t)
      case _ => t update subres
    }
}

////////////////////////////////////////////////////////////////////////////////
// There are two implementations of the class to represent variable
// permutations: one that is dense, and uses lists, and one that is sparse

object IVarShift {
  protected[parser] val AC = Debug.AC_INPUT_ABSY
  
  def apply(prefix : List[Int], defaultShift : Int) =
    IVarShiftList(prefix, defaultShift)
  
  def apply(prefix : Map[Int, Int], defaultShift : Int) =
    IVarShiftMapEmptyPrefix(0, prefix, defaultShift)
  
  def apply(mapping : Map[IVariable, IVariable],
            defaultShift : Int) : IVarShift = {
    val intMapping =
      for ((IVariable(i), IVariable(j)) <- mapping) yield (i -> (j - i))
    IVarShiftMapEmptyPrefix(0, intMapping, defaultShift)
  }
}

abstract class IVarShift {
  
  def push(n : Int) : IVarShift
  def pop : IVarShift
  
  def isIdentity : Boolean

  def apply(i : Int) : Int
  
  def apply(v : IVariable) : IVariable = {
    val newIndex = apply(v.index)
    if (newIndex == v.index) v else IVariable(newIndex)
  }
}

case class IVarShiftList(prefix : List[Int], defaultShift : Int)
           extends IVarShift {
  
  lazy val length = prefix.length
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IVarShift.AC,
                   defaultShift + length >= 0 &&
                   (prefix.iterator.zipWithIndex forall {case (i, j) => i + j >= 0}))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def push(n : Int) = IVarShiftList(n :: prefix, defaultShift)
  
  def pop = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, !prefix.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    IVarShiftList(prefix.tail, defaultShift)
  }
  
  def compose(that : IVarShiftList) : IVarShift = {
    val newPrefix = new scala.collection.mutable.ArrayBuffer[Int]
    for ((o, i) <- that.prefix.iterator.zipWithIndex)
      newPrefix += (apply(i + o) - i)
    for (i <- that.length until (this.length - that.defaultShift))
      newPrefix += (apply(i + that.defaultShift) - i)
    IVarShiftList(newPrefix.toList, this.defaultShift + that.defaultShift)
  }
  
  def isIdentity : Boolean =
    defaultShift == 0 && (prefix forall (_ == 0))

  def apply(i : Int) : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, i >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    i + (if (i < length) prefix(i) else defaultShift)
  }

}

case class IVarShiftMap(prefix : List[Int],
                        mapping : Map[Int, Int],
                        defaultShift : Int)
           extends IVarShift {
  
  lazy val prefixLength = prefix.length
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IVarShift.AC,
    (defaultShift >= 0 || ((0 until -defaultShift) forall (mapping contains _))) &&
    (prefix.iterator.zipWithIndex forall {case (i, j) => i + j >= 0}) &&
    (mapping forall {case (i, j) => i + j >= 0}))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def push(n : Int) =
    IVarShiftMap(n :: prefix, mapping, defaultShift)
  
  def pop = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, !prefix.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    IVarShiftMap(prefix.tail, mapping, defaultShift)
  }
  
  def isIdentity : Boolean =
    defaultShift == 0 &&
    (prefix forall (_ == 0)) &&
    (mapping.values forall (_ == 0))

  def apply(i : Int) : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, i >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    i + (if (i < prefixLength)
           prefix(i)
         else
           mapping.getOrElse(i - prefixLength, defaultShift))
  }

}

/**
 * Special case for a prefix only containing zeroes
 */
case class IVarShiftMapEmptyPrefix(prefixLength : Int,
                                   mapping : Map[Int, Int],
                                   defaultShift : Int)
           extends IVarShift {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IVarShift.AC,
    (defaultShift >= 0 || ((0 until -defaultShift) forall (mapping contains _))) &&
    (mapping forall {case (i, j) => i + j >= 0}))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def push(n : Int) =
    if (n == 0)
      IVarShiftMapEmptyPrefix(prefixLength + 1, mapping, defaultShift)
    else
      IVarShiftMap(n :: List.fill(prefixLength)(0), mapping, defaultShift)
  
  def pop = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, prefixLength > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    IVarShiftMapEmptyPrefix(prefixLength - 1, mapping, defaultShift)
  }
  
  def isIdentity : Boolean =
    defaultShift == 0 && (mapping.values forall (_ == 0))

  def apply(i : Int) : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IVarShift.AC, i >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (i < prefixLength)
      i
    else
      i + mapping.getOrElse(i - prefixLength, defaultShift)
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Substitute some of the constants in an expression with arbitrary terms
 */
object ConstantSubstVisitor
       extends CollectingVisitor[(CMap[ConstantTerm, ITerm], Int), IExpression] {
  import IExpression.i
         
  def apply(t : IExpression, subst : CMap[ConstantTerm, ITerm]) : IExpression =
    ConstantSubstVisitor.visit(t, (subst, 0))
  def apply(t : ITerm, subst : CMap[ConstantTerm, ITerm]) : ITerm =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[ITerm]
  def apply(t : IFormula, subst : CMap[ConstantTerm, ITerm]) : IFormula =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[IFormula]

  def rename(t : ITerm, subst : CMap[ConstantTerm, ConstantTerm]) : ITerm =
    apply(t.asInstanceOf[IExpression], subst mapValues (i(_))).asInstanceOf[ITerm]
  def rename(t : IFormula, subst : CMap[ConstantTerm, ConstantTerm]) : IFormula =
    apply(t.asInstanceOf[IExpression], subst mapValues (i(_))).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        subst : (CMap[ConstantTerm, ITerm], Int)) : PreVisitResult =
    t match {
      case IConstant(c) => ShortCutResult((subst._1 get c) match {
        case Some(replacement) => VariableShiftVisitor(replacement, 0, subst._2)
        case None => t
      })
      case _ : IQuantified | _ : IEpsilon =>
        UniSubArgs((subst._1, subst._2 + 1))
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                subst : (CMap[ConstantTerm, ITerm], Int),
                subres : Seq[IExpression]) : IExpression = t update subres
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Substitute some predicates in an expression with arbitrary formulae
 */
object PredicateSubstVisitor
       extends CollectingVisitor[(CMap[Predicate, IFormula], Int), IExpression] {
  def apply(t : IExpression, subst : CMap[Predicate, IFormula]) : IExpression =
    PredicateSubstVisitor.visit(t, (subst, 0))
  def apply(t : ITerm, subst : CMap[Predicate, IFormula]) : ITerm =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[ITerm]
  def apply(t : IFormula, subst : CMap[Predicate, IFormula]) : IFormula =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        subst : (CMap[Predicate, IFormula], Int)) : PreVisitResult =
    t match {
      case IAtom(p, _) => (subst._1 get p) match {
        case Some(replacement) => ShortCutResult(VariableShiftVisitor(replacement, 0, subst._2))
        case None => KeepArg
      }
      case _ : IQuantified | _ : IEpsilon =>
        UniSubArgs((subst._1, subst._2 + 1))
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                subst : (CMap[Predicate, IFormula], Int),
                subres : Seq[IExpression]) : IExpression = t update subres
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Substitute variables in an expression with arbitrary terms
 */
object VariableSubstVisitor
       extends CollectingVisitor[(List[ITerm], Int), IExpression] {
  def apply(t : IExpression, substShift : (List[ITerm], Int)) : IExpression =
    VariableSubstVisitor.visit(t, substShift)
  def apply(t : ITerm, substShift : (List[ITerm], Int)) : ITerm =
    apply(t.asInstanceOf[IExpression], substShift).asInstanceOf[ITerm]
  def apply(t : IFormula, substShift : (List[ITerm], Int)) : IFormula =
    apply(t.asInstanceOf[IExpression], substShift).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        substShift : (List[ITerm], Int)) : PreVisitResult =
    t match {
      case IVariable(index) => {
        val (subst, shift) = substShift
        ShortCutResult(if (index >= subst.size)
                         IVariable(index + shift)
                       else
                         subst(index))
      }
      case _ : IQuantified | _ : IEpsilon => {
        val (subst, shift) = substShift
        val newSubst = for (t <- subst) yield VariableShiftVisitor(t, 0, 1)
        UniSubArgs((IVariable(0) :: newSubst, shift))
      }
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                substShift : (List[ITerm], Int),
                subres : Seq[IExpression]) : IExpression = t update subres
}

////////////////////////////////////////////////////////////////////////////////

object SymbolCollector {
  def variables(t : IExpression) : scala.collection.Set[IVariable] = {
    val variables = new MHashSet[IVariable]
    val c = new SymbolCollector (variables, null, null)
    c.visitWithoutResult(t, 0)
    variables
  }
  def constants(t : IExpression) : scala.collection.Set[ConstantTerm] = {
    val constants = new MHashSet[ConstantTerm]
    val c = new SymbolCollector(null, constants, null)
    c.visitWithoutResult(t, 0)
    constants
  }
  def constantsSorted(t : IExpression) : Seq[ConstantTerm] = {
    val constants = new LinkedHashSet[ConstantTerm]
    val c = new SymbolCollector(null, constants, null)
    c.visitWithoutResult(t, 0)
    constants.toSeq
  }
  def nullaryPredicates(t : IExpression) : scala.collection.Set[Predicate] = {
    val predicates = new MHashSet[Predicate]
    val c = new SymbolCollector(null, null, predicates)
    c.visitWithoutResult(t, 0)
    predicates
  }
  def varsConstsPreds(t : IExpression)
      : (scala.collection.Set[IVariable],
         scala.collection.Set[ConstantTerm],
         scala.collection.Set[Predicate]) = {
    val variables = new MHashSet[IVariable]
    val constants = new MHashSet[ConstantTerm]
    val predicates = new MHashSet[Predicate]
    val c = new SymbolCollector(variables, constants, predicates)
    c.visitWithoutResult(t, 0)
    (variables, constants, predicates)
  }
}

class SymbolCollector(variables : scala.collection.mutable.Set[IVariable],
                      constants : scala.collection.mutable.Set[ConstantTerm],
                      nullaryPredicates : scala.collection.mutable.Set[Predicate])
      extends CollectingVisitor[Int, Unit] {

  override def preVisit(t : IExpression, boundVars : Int) : PreVisitResult =
    t match {
      case _ : IQuantified | _ : IEpsilon => UniSubArgs(boundVars + 1)
      case _ => KeepArg
    }

  def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
    t match {
      case IVariable(i) if (variables != null && i >= boundVars) =>
        variables += IVariable(i - boundVars)
      case IConstant(c) if (constants != null) =>
        constants += c
      case IAtom(p, Seq()) if (nullaryPredicates != null) =>
        nullaryPredicates += p
      case _ => // nothing
    }
}

////////////////////////////////////////////////////////////////////////////////

object VariableIndexCollector
       extends CollectingVisitor[(Int, Int => Unit), Unit] {

  def apply(t : IExpression, f : Int => Unit) : Unit =
    this.visitWithoutResult(t, (0, f))

  override def preVisit(t : IExpression,
                        ctxt : (Int, Int => Unit)) : PreVisitResult = t match {
    case _ : IQuantified | _ : IEpsilon => UniSubArgs((ctxt._1 + 1, ctxt._2))
    case _ => KeepArg
  }

  def postVisit(t : IExpression,
                ctxt : (Int, Int => Unit),
                subres : Seq[Unit]) : Unit = t match {
    case IVariable(i) => {
      val (boundVars, f) = ctxt
      if (i >= boundVars)
        f(i - boundVars)
    }
    case _ => // nothing
  }
    
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Check whether an expression contains some <code>IVariable</code>,
 * <code>IConstant</code>, <code>IAtom</code>, or <code>IFunApp</code>.
 */
object ContainsSymbol extends ContextAwareVisitor[IExpression => Boolean, Unit] {
  
  def freeFrom(t : IExpression, syms : Set[IVariable]) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case v : IVariable => syms contains v
       case _ => false
     })
  
  def apply(t : IExpression, pred : IExpression => Boolean) : Boolean = try {
    visitWithoutResult(t, Context(pred))
    false
  } catch {
    case FOUND_EXCEPTION => true
  }
  
  def apply(t : IExpression, searchExpr : IExpression) : Boolean = try {
    visitWithoutResult(t, Context(_ == searchExpr))
    false
  } catch {
    case FOUND_EXCEPTION => true
  }
  
  private object FOUND_EXCEPTION extends Exception
  
  override def preVisit(t : IExpression,
                        context : Context[IExpression => Boolean]) : PreVisitResult = {
    t match {
      case v : IVariable =>
        if (context.binders.isEmpty) {
          if (context.a(v))
            throw FOUND_EXCEPTION
        } else {
          val newIndex = v.index - context.binders.size
          if (newIndex >= 0 && context.a(IVariable(newIndex)))
            throw FOUND_EXCEPTION
        }
      case _ : IConstant | _ : IAtom | _ : IFunApp =>
        if (context.a(t))
          throw FOUND_EXCEPTION
      case _ => // nothing
    }
    super.preVisit(t, context)
  }

  def postVisit(t : IExpression,
                context : Context[IExpression => Boolean],
                subres : Seq[Unit]) : Unit = ()
}

////////////////////////////////////////////////////////////////////////////////

object Context {
  abstract sealed class Binder {
    def toQuantifier : Quantifier = throw new UnsupportedOperationException
  }
  case object ALL extends Binder {
    override def toQuantifier = Quantifier.ALL
  }
  case object EX extends Binder {
    override def toQuantifier = Quantifier.EX
  }
  case object EPS extends Binder
  
  def toBinder(q : Quantifier) = q match {
    case Quantifier.ALL => ALL
    case Quantifier.EX => EX
  }
  
  def apply[A](a : A) : Context[A] = Context(List(), +1, a)
}

case class Context[A](binders : List[Context.Binder], polarity : Int, a : A) {
  import Context._
  
  def togglePolarity = Context(binders, -polarity, a)
  def noPolarity = Context(binders, 0, a)
  def push(q : Quantifier) = Context(toBinder(q) :: binders, polarity, a)
  def push(b : Binder) = Context(b :: binders, polarity, a)
  def apply(newA : A) = Context(binders, polarity, newA)
}

abstract class ContextAwareVisitor[A, R] extends CollectingVisitor[Context[A], R] {

  override def preVisit(t : IExpression, arg : Context[A]) : PreVisitResult =
    t match {
      case INot(_) => UniSubArgs(arg.togglePolarity)
      case IBinFormula(IBinJunctor.Eqv, _, _) => UniSubArgs(arg.noPolarity)
      case IQuantified(quan, _) => {
        val actualQuan = if (arg.polarity < 0) quan.dual else quan
        UniSubArgs(arg push actualQuan)
      }
      case IEpsilon(_) => UniSubArgs(arg push Context.EPS)
      case _ => UniSubArgs(arg) // a subclass might have overridden this method
                                // and substituted a different context
    }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Push negations down to the atoms in a formula
 */
object Transform2NNF extends CollectingVisitor[Boolean, IExpression] {
  import IExpression._
  import IBinJunctor._
  
  def apply(f : IFormula) : IFormula =
    this.visit(f, false).asInstanceOf[IFormula]
    
  override def preVisit(t : IExpression, negate : Boolean) : PreVisitResult =
    t match {
      case INot(f) => TryAgain(f, !negate)  // eliminate negations
      case t@IBoolLit(b) => ShortCutResult(if (negate) !b else t)
      case LeafFormula(s) => UniSubArgs(false)
      case IBinFormula(Eqv, _, _) => SubArgs(List(negate, false))
      case ITrigger(ts, _) => SubArgs(List.fill(ts.size){false} ::: List(negate))
      case _ : IFormulaITE => SubArgs(List(false, negate, negate))
      case _ : IFormula => KeepArg
      case _ : ITerm => KeepArg
    }

  def postVisit(t : IExpression, negate : Boolean,
                subres : Seq[IExpression]) : IExpression =
    if (negate) t match {
      case IBinFormula(Eqv, _, _) | _ : ITrigger | _ : INamedPart |
           _ : IFormulaITE =>
        t update subres
      case IBinFormula(And, _, _) =>
        subres(0).asInstanceOf[IFormula] | subres(1).asInstanceOf[IFormula]
      case IBinFormula(Or, _, _) =>
        subres(0).asInstanceOf[IFormula] & subres(1).asInstanceOf[IFormula]
      case IQuantified(quan, _) =>
        IQuantified(quan.dual, subres(0).asInstanceOf[IFormula])
      case LeafFormula(t) =>
        !(t.asInstanceOf[IFormula] update subres)
    } else {
      t update subres
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Turn a formula <code> f1 &lowast; f2 &lowast; ... &lowast; fn </code>
 * (where <code>&lowast;</code> is some binary operator) into
 * <code>List(f1, f2, ..., fn)</code>
 */
object LineariseVisitor {
  def apply(t : IFormula, op : IBinJunctor.Value) : Seq[IFormula] = {
    val parts = scala.collection.mutable.ArrayBuilder.make[IFormula]
  
    val visitor = new CollectingVisitor[Unit, Unit] {
      override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = t match {
        case IBinFormula(`op`, _, _) =>
          KeepArg
        case t : IFormula => {
          parts += t
          ShortCutResult({})
        }
      }

      def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = {}
    }
    
    visitor.visitWithoutResult(t, {})
    parts.result
  }
}

////////////////////////////////////////////////////////////////////////////////

object QuantifierCountVisitor {
  def apply(f : IFormula) : Int = {
    val v = new QuantifierCountVisitor
    v.visitWithoutResult(f, {})
    v.count
  }
}

/**
 * Count the number of quantifiers in a formula
 */
class QuantifierCountVisitor extends CollectingVisitor[Unit, Unit] {
  private var count = 0

  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[Unit]) : Unit = t match {
    case t : IQuantified => count = count + 1
    case _ => // nothing
  }
}

////////////////////////////////////////////////////////////////////////////////

object Transform2Prenex {
  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : IFormula = {
    val quantifierNum = QuantifierCountVisitor(f)
    if (quantifierNum == 0) {
      f
    } else {
      val v = new Transform2Prenex(quantifierNum)
      val quantifierFree =
        v.visit(f, Context(List[IVariable]())).asInstanceOf[IFormula]
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, quantifierNum == v.quantifiersToAdd.size)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      IExpression.quan(v.quantifiersToAdd, quantifierFree)
    }
  }
}

/**
 * Turn a formula into prenex form.
 */
class Transform2Prenex private (finalQuantifierNum : Int)
      extends ContextAwareVisitor[List[IVariable], IExpression] {

  private val quantifiersToAdd = new ArrayBuffer[Quantifier]

  override def preVisit(t : IExpression,
                        context : Context[List[IVariable]])
                       : PreVisitResult = t match {
    case IQuantified(q, _) => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(Transform2Prenex.AC, context.polarity != 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val newVars = IVariable(finalQuantifierNum - quantifiersToAdd.size - 1) :: context.a
      quantifiersToAdd += (if (context.polarity > 0) q else q.dual)
      super.preVisit(t, context(newVars))
    }
    case _ : IEpsilon => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // case that we don't expect here
      Debug.assertInt(Transform2Prenex.AC, false)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      null
    }
    case _ => super.preVisit(t, context)
  }

  def postVisit(t : IExpression, context : Context[List[IVariable]],
                subres : Seq[IExpression]) : IExpression = t match {
    case v@IVariable(ind)  => {
      val newVar =
        if (ind >= context.a.size)
          IVariable(ind - context.a.size + finalQuantifierNum)
        else
          context.a(ind)
      if (newVar == v) v else newVar
    }
    case _ : IQuantified =>
      subres(0)
    case _               =>
      t update subres
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Compute the number of operators in an expression.
 */
object SizeVisitor {
  def apply(e : IExpression) : Int = {
    var size = 0
    
    val visitor = new CollectingVisitor[Unit, Unit] {
      def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit =
        size = size + 1
    }
    
    visitor.visitWithoutResult(e, {})
    size
  }
}
