/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import IExpression.{ConstantTerm, Predicate, Sort}
import ap.terfor.conjunctions.Quantifier
import ap.theories.{TheoryRegistry, ModuloArithmetic, ADT, Theory, MulTheory}
import ap.util.{Debug, Logic, PlainRange, Seqs}

import scala.collection.mutable.{ArrayStack => Stack, ArrayBuffer,
                                 LinkedHashSet, HashSet => MHashSet,
                                 HashMap => MHashMap}
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
                  Debug.assertInt(CollectingVisitor.AC,
                                 subArgs.length == expr.length)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  for (i <- (expr.length - 1) to 0 by -1)
                    argsToVisit push subArgs(i)
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
                  Debug.assertInt(CollectingVisitor.AC,
                                  subArgs.length == expr.length)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  for (i <- (expr.length - 1) to 0 by -1)
                    argsToVisit push subArgs(i)
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

/**
 * Visitor to shift all variables with <code>index >= offset</code> by
 * <code>shift</code>.
 */
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

/**
 * Visitor to shift all variables with <code>index >= offset</code> by
 * <code>shift</code>.
 */
class VariableShiftVisitor(offset : Int, shift : Int)
      extends CollectingVisitor[Int, IExpression] {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(VariableShiftVisitor.AC, offset >= 0 && offset + shift >= 0)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  override def preVisit(t : IExpression, quantifierNum : Int) : PreVisitResult =
    t match {
      case _ : IVariableBinder => UniSubArgs(quantifierNum + 1)
      case _ => KeepArg
    }
  def postVisit(t : IExpression, quantifierNum : Int,
                subres : Seq[IExpression]) : IExpression =
    t match {
      case t : IVariable =>
        if (t.index < offset + quantifierNum) t else (t shiftedBy shift)
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
      case _ : IVariableBinder => UniSubArgs(shifts push 0)
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
    if (newIndex == v.index) v else ISortedVariable(newIndex, v.sort)
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
      case _ : IVariableBinder =>
        UniSubArgs((subst._1, subst._2 + 1))
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                subst : (CMap[ConstantTerm, ITerm], Int),
                subres : Seq[IExpression]) : IExpression = t update subres
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Substitute some of the constants in an expression with arbitrary terms,
 * and immediately simplify the resulting expression if possible.
 */
object SimplifyingConstantSubstVisitor
       extends CollectingVisitor[(CMap[ConstantTerm, ITerm], Int), IExpression] {
  import IExpression.i
         
  def apply(t : IExpression, subst : CMap[ConstantTerm, ITerm]) : IExpression =
    SimplifyingConstantSubstVisitor.visit(t, (subst, 0))
  def apply(t : ITerm, subst : CMap[ConstantTerm, ITerm]) : ITerm =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[ITerm]
  def apply(t : IFormula, subst : CMap[ConstantTerm, ITerm]) : IFormula =
    apply(t.asInstanceOf[IExpression], subst).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        subst : (CMap[ConstantTerm, ITerm], Int)) : PreVisitResult =
    t match {
      case IConstant(c) => ShortCutResult((subst._1 get c) match {
        case Some(replacement) => VariableShiftVisitor(replacement, 0, subst._2)
        case None => t
      })
      case _ : IVariableBinder =>
        UniSubArgs((subst._1, subst._2 + 1))
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                subst : (CMap[ConstantTerm, ITerm], Int),
                subres : Seq[IExpression]) : IExpression =
    IExpression.updateAndSimplifyLazily(t, subres)
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
      case _ : IVariableBinder =>
        UniSubArgs((subst._1, subst._2 + 1))
      case _ => KeepArg
    }

  def postVisit(t : IExpression,
                subst : (CMap[Predicate, IFormula], Int),
                subres : Seq[IExpression]) : IExpression = t update subres
}

////////////////////////////////////////////////////////////////////////////////

object UniformSubstVisitor {
  def apply(t : IFormula, subst : CMap[Predicate, IFormula]) : IFormula = {
    val visitor = new UniformSubstVisitor(subst)
    visitor.visit(t.asInstanceOf[IExpression], ()).asInstanceOf[IFormula]
  }
}

/**
 * Uniform substitution of predicates: replace all occurrences of predicates
 * with a formula; the replacement of an n-ary predicate can contain free variables
 * <code>_0, _1, ..., _(n-1)</code> which are replaced with the predicate arguments.
 */
class UniformSubstVisitor(subst : CMap[Predicate, IFormula])
      extends CollectingVisitor[Unit, IExpression] {

  def postVisit(t : IExpression,
                arg : Unit,
                subres : Seq[IExpression]) : IExpression = t match {
    case a@IAtom(p, _) => (subst get p) match {
      case Some(replacement) =>
        VariableSubstVisitor(
          replacement,
          ((for (e <- subres) yield e.asInstanceOf[ITerm]).toList, 0))
      case None =>
        a update subres
    }
    case _ =>
      t update subres
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor to replace occurrences of one expression with another expression.
 */
object ExpressionReplacingVisitor
       extends CollectingVisitor[(IExpression, IExpression), IExpression] {

  def apply(f : IFormula,
            replaced : IExpression, replaceWith : IExpression) =
    visit(f, (replaced, replaceWith)).asInstanceOf[IFormula]

  def apply(f : ITerm,
            replaced : IExpression, replaceWith : IExpression) =
    visit(f, (replaced, replaceWith)).asInstanceOf[ITerm]

  def apply(f : IExpression,
            replaced : IExpression, replaceWith : IExpression) =
    visit(f, (replaced, replaceWith))

  override def preVisit(t : IExpression,
                        arg : (IExpression, IExpression)) : PreVisitResult =
    t match {
      case t : IVariableBinder =>
        UniSubArgs((IExpression.shiftVars(arg._1, 0, 1),
                    IExpression.shiftVars(arg._2, 0, 1)))
      case _ =>
        KeepArg
    }
    
  def postVisit(t : IExpression,
                arg : (IExpression, IExpression),
                subres : Seq[IExpression]) : IExpression = {
    val res = t update subres
    if (res == arg._1)
      arg._2
    else
      res
  }

}


////////////////////////////////////////////////////////////////////////////////

abstract class AbstractVariableSubstVisitor
               extends CollectingVisitor[(List[ITerm], Int), IExpression] {
  def apply(t : IExpression, substShift : (List[ITerm], Int)) : IExpression =
    visit(t, substShift)
  def apply(t : ITerm, substShift : (List[ITerm], Int)) : ITerm =
    apply(t.asInstanceOf[IExpression], substShift).asInstanceOf[ITerm]
  def apply(t : IFormula, substShift : (List[ITerm], Int)) : IFormula =
    apply(t.asInstanceOf[IExpression], substShift).asInstanceOf[IFormula]

  override def preVisit(t : IExpression,
                        substShift : (List[ITerm], Int)) : PreVisitResult =
    t match {
      case t : IVariable => {
        val (subst, shift) = substShift
        ShortCutResult(if (t.index >= subst.size)
                         t shiftedBy shift
                       else
                         subst(t.index))
      }
      case t : IVariableBinder => {
        val (subst, shift) = substShift
        val newSubst = for (t <- subst) yield VariableShiftVisitor(t, 0, 1)
        UniSubArgs((ISortedVariable(0, t.sort) :: newSubst, shift))
      }
      case _ => KeepArg
    }
}

/**
 * Substitute variables in an expression with arbitrary terms
 */
object VariableSubstVisitor extends AbstractVariableSubstVisitor {
  def postVisit(t : IExpression,
                substShift : (List[ITerm], Int),
                subres : Seq[IExpression]) : IExpression =
    t update subres
}

/**
 * Substitute variables in an expression with arbitrary terms,
 * and immediately simplify the resulting expression if possible.
 */
object SimplifyingVariableSubstVisitor extends AbstractVariableSubstVisitor {
  def postVisit(t : IExpression,
                substShift : (List[ITerm], Int),
                subres : Seq[IExpression]) : IExpression =
    IExpression.updateAndSimplifyLazily(t, subres)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for collecting the variables, constants, or nullary predicates
 * occurring in an expression.
 */
object SymbolCollector {
  def variables(t : IExpression) : scala.collection.Set[IVariable] = {
    val variables = new MHashSet[IVariable]
    val c = new SymbolCollector (variables, null, null)
    c.visitWithoutResult(t, 0)
    variables
  }
  def variablesSorted(t : IExpression) : scala.collection.Seq[IVariable] = {
    val variables = new LinkedHashSet[IVariable]
    val c = new SymbolCollector (variables, null, null)
    c.visitWithoutResult(t, 0)
    variables.toSeq
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

/**
 * Class for collecting the variables, constants, or nullary predicates
 * occurring in an expression.
 */
class SymbolCollector(variables : scala.collection.mutable.Set[IVariable],
                      constants : scala.collection.mutable.Set[ConstantTerm],
                      nullaryPredicates : scala.collection.mutable.Set[Predicate])
      extends CollectingVisitor[Int, Unit] {

  override def preVisit(t : IExpression, boundVars : Int) : PreVisitResult =
    t match {
      case _ : IVariableBinder => UniSubArgs(boundVars + 1)
      case _ => KeepArg
    }

  def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
    t match {
      case t@IVariable(i) if (variables != null && i >= boundVars) =>
        variables += t shiftedBy (-boundVars)
      case IConstant(c) if (constants != null) =>
        constants += c
      case IAtom(p, Seq()) if (nullaryPredicates != null) =>
        nullaryPredicates += p
      case _ => // nothing
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for collecting the functions occurring in an expression.
 */
object FunctionCollector {
  def apply(t : IExpression) : scala.collection.Set[IFunction] = {
    val functions = new MHashSet[IFunction]
    val c = new FunctionCollector (functions)
    c.visitWithoutResult(t, 0)
    functions
  }
  def apply(ts : Iterable[IExpression]) : scala.collection.Set[IFunction] = {
    val functions = new MHashSet[IFunction]
    val c = new FunctionCollector (functions)
    for (t <- ts)
      c.visitWithoutResult(t, 0)
    functions
  }
}

/**
 * Class for collecting the functions occurring in an expression.
 */
class FunctionCollector(functions : scala.collection.mutable.Set[IFunction])
      extends CollectingVisitor[Int, Unit] {
  def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
    t match {
      case IFunApp(f, _) => functions += f
      case _ => // nothing
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for collecting the indexes of free variables occurring in an
 * expression.
 */
object VariableIndexCollector
       extends CollectingVisitor[(Int, Int => Unit), Unit] {

  /**
   * Traverse the given expression, and invoke <code>f(n)</code> whenever
   * a variable with index <code>n</code> is encountered.
   */
  def apply(t : IExpression, f : Int => Unit) : Unit =
    this.visitWithoutResult(t, (0, f))

  override def preVisit(t : IExpression,
                        ctxt : (Int, Int => Unit)) : PreVisitResult = t match {
    case _ : IVariableBinder => UniSubArgs((ctxt._1 + 1, ctxt._2))
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
object ContainsSymbol extends ContextAwareVisitor[IExpression => Boolean, Unit]{
  
  /**
   * Check that given expression does not contain any of the variables.
   */
  def freeFrom(t : IExpression, syms : Set[IVariable]) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case v : IVariable => syms contains v
       case _ => false
     })
  
  /**
   * Check that given expression does not contain any of the variables.
   */
  def freeFromVariableIndex(t : IExpression, indexes : Set[Int]) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case v : IVariable => indexes contains v.index
       case _ => false
     })

  /**
   * Check that given expression only contains variables with index at
   * least <code>threshold</code>.
   */
  def allVariablesAtLeast(t : IExpression, threshold : Int) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case v : IVariable => v.index < threshold
       case _ => false
     })
  
  /**
   * Check that given expression does not contain free/unbound variables.
   */
  def isClosed(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case v : IVariable => true
       case _ => false
     })

  /**
   * Check whether the given expression is in Presburger arithmetic.
   */
  def isPresburger(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case _ : IFunApp | _ : IAtom => true
       case _ => false
     })

  /**
   * Check whether the given expression contains any functions
   * (instances of <code>IFunApp</code>).
   */
  def containsFunctions(t : IExpression) : Boolean =
    apply(t, (x:IExpression) => x match {
       case _ : IFunApp => true
       case _ => false
     })

  /**
   * Check whether the given expression contains some predicate.
   */
  def containsPredicate(t : IExpression, p : Predicate) : Boolean =
    apply(t, (x:IExpression) => x match {
       case IAtom(`p`, _) => true
       case _ => false
     })

  /**
   * Check whether given formula is in Presburger or bit-vector arithmetic.
   */
  def isPresburgerBV(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case IFunApp(f, _) =>
         (TheoryRegistry lookupSymbol f) match {
           case Some(t) => !isPresburgerBVTheory(t)
           case _       => true
         }
       case IAtom(p, _) =>
         (TheoryRegistry lookupSymbol p) match {
           case Some(t) => !isPresburgerBVTheory(t)
           case _       => true
         }
       case _ => false
     })

  private def isPresburgerBVTheory(t : Theory) = t match {
    case ModuloArithmetic => true
    case ADT.BoolADT      => true
    case _                => false
  }

  /**
   * Check whether given formula is in Presburger, bit-vector, or
   * non-linear arithmetic.
   */
  def isPresburgerBVNonLin(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case IFunApp(f, _) =>
         (TheoryRegistry lookupSymbol f) match {
           case Some(t) => !isPresburgerBVNonLinTheory(t)
           case _       => true
         }
       case IAtom(p, _) =>
         (TheoryRegistry lookupSymbol p) match {
           case Some(t) => !isPresburgerBVNonLinTheory(t)
           case _       => true
         }
       case _ => false
     })

  private def isPresburgerBVNonLinTheory(t : Theory) = t match {
    case ModuloArithmetic => true
    case ADT.BoolADT      => true
    case _ : MulTheory    => true
    case _                => false
  }

  /**
   * Check whether given formula is in Presburger arithmetic, but
   * possibly including predicate atoms in which all arguments
   * are concrete numbers.
   */
  def isPresburgerWithPreds(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case _ : IFunApp => true
       case IAtom(_, args) => !(args forall (_.isInstanceOf[IIntLit]))
       case _ => false
     })

  /**
   * Check whether given formula is in Presburger or bit-vector arithmetic, but
   * possibly including predicate atoms in which all arguments
   * are concrete numbers.
   */
  def isPresburgerBVWithPreds(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case IFunApp(f, _) =>
         (TheoryRegistry lookupSymbol f) match {
           case Some(t) => !isPresburgerBVTheory(t)
           case _       => true
         }
       case IAtom(p, args) =>
         (TheoryRegistry lookupSymbol p) match {
           case Some(t) => !isPresburgerBVTheory(t)
           case _       => !(args forall (_.isInstanceOf[IIntLit]))
         }
       case _ =>
         false
     })

  /**
   * Check whether given formula is in Presburger, bit-vector, or
   * non-linear arithmetic, but possibly including predicate atoms in
   * which all arguments are concrete numbers.
   */
  def isPresburgerBVNonLinWithPreds(t : IExpression) : Boolean =
    !apply(t, (x:IExpression) => x match {
       case IFunApp(f, _) =>
         (TheoryRegistry lookupSymbol f) match {
           case Some(t) => !isPresburgerBVNonLinTheory(t)
           case _       => true
         }
       case IAtom(p, args) =>
         (TheoryRegistry lookupSymbol p) match {
           case Some(t) => !isPresburgerBVNonLinTheory(t)
           case _       => !(args forall (_.isInstanceOf[IIntLit]))
         }
       case _ =>
         false
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
                        context : Context[IExpression => Boolean])
                      : PreVisitResult = {
    t match {
      case v : IVariable =>
        if (context.binders.isEmpty) {
          if (context.a(v))
            throw FOUND_EXCEPTION
        } else {
          val shift = context.binders.size
          if (v.index >= shift && context.a(v shiftedBy (-shift)))
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

/**
 * Check whether an expression contains the variable with index
 * <code>index</code>.
 */
object ContainsVariable {
  def apply(e : IExpression, index : Int) : Boolean =
    !ContainsSymbol.freeFromVariableIndex(e, Set(index))
}

/**
 * Check whether the given expression contains some predicate.
 */
object ContainsPredicate {
  def apply(e : IExpression, p : Predicate) : Boolean =
    ContainsSymbol.containsPredicate(e, p)
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
  
  def apply[A](a : A) : Context[A] = Context(List(), List(), +1, a)
}

case class Context[A](binders : List[Context.Binder],
                      boundSorts : List[IExpression.Sort],
                      polarity : Int,
                      a : A) {
  import Context._
  import IExpression._
  
  def togglePolarity =
    Context(binders, boundSorts, -polarity, a)
  def noPolarity =
    Context(binders, boundSorts, 0, a)
  def push(q : Quantifier, sort : Sort) =
    Context(toBinder(q) :: binders, sort :: boundSorts, polarity, a)
  def push(b : Binder, sort : Sort) =
    Context(b :: binders, sort :: boundSorts, polarity, a)
  def apply(newA : A) =
    Context(binders, boundSorts, polarity, newA)
}

/**
 * An extended version of the <code>CollectingVisitor</code> that also keeps
 * track of the sign of a sub-expression (positive or negative), and of the
 * bound variables.
 */
abstract class ContextAwareVisitor[A, R]
         extends CollectingVisitor[Context[A], R] {

  override def preVisit(t : IExpression, arg : Context[A]) : PreVisitResult =
    t match {
      case INot(_) =>
        UniSubArgs(arg.togglePolarity)
      case IBinFormula(IBinJunctor.Eqv, _, _) =>
        UniSubArgs(arg.noPolarity)
      case ISortedQuantified(quan, sort, _) => {
        val actualQuan = if (arg.polarity < 0) quan.dual else quan
        UniSubArgs(arg.push(actualQuan, sort))
      }
      case ISortedEpsilon(sort, _) =>
        UniSubArgs(
          Context(Context.EPS :: arg.binders,
                  sort :: arg.boundSorts, -1, arg.a))
      case IFormulaITE(_, _, _) | ITermITE(_, _, _) =>
        SubArgs(List(arg.noPolarity, arg, arg))
      case _ =>
        UniSubArgs(arg) // a subclass might have overridden this method
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
      case ISortedQuantified(quan, sort, _) =>
        ISortedQuantified(quan.dual, sort, subres(0).asInstanceOf[IFormula])
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
  protected[parser] val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : Int = {
    val v = new QuantifierCountVisitor
    v.visitWithoutResult(f, {})
    v.count
  }
  def apply(f : IFormula, consideredQuantifiers : Set[Quantifier]) : Int = {
    val v = new SelectiveQuantifierCountVisitor (consideredQuantifiers)
    v.visitWithoutResult(f, Context({}))
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

/**
 * Count the number of quantifiers in a formula
 */
class SelectiveQuantifierCountVisitor(consideredQuantifiers : Set[Quantifier])
      extends ContextAwareVisitor[Unit, Unit] {
  protected[parser] var count = 0

  override def preVisit(t : IExpression,
                        ctxt : Context[Unit]) : PreVisitResult = t match {
    case IQuantified(q, _) => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(QuantifierCountVisitor.AC, ctxt.polarity != 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val realQuan = if (ctxt.polarity > 0) q else q.dual
      if (consideredQuantifiers contains realQuan) {
        count = count + 1
        super.preVisit(t, ctxt)
      } else {
        ShortCutResult(())
      }
    }
    case _ => super.preVisit(t, ctxt)
  }

  def postVisit(t : IExpression, ctxt : Context[Unit],
                subres : Seq[Unit]) : Unit = ()
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor for checking whether a formula contains any existential
 * quantifiers without explicitly specified triggers.
 *
 * TODO: this does not capture all cases, and has quadratic
 * complexity, should be revised.
 */
object IsUniversalFormulaVisitor extends ContextAwareVisitor[Unit, Unit] {

  private object FoundQuantifier extends Exception
  private val v0Set = Set(0)

  import IExpression.Eq

  def apply(f : IExpression) : Boolean = try {
    this.visitWithoutResult(f, Context({}))
    true
  } catch {
    case FoundQuantifier => false
  }

  private def isEX(q : Quantifier, polarity : Int) = q match {
    case Quantifier.EX  if polarity >= 0 => true
    case Quantifier.ALL if polarity <= 0 => true
    case _ => false
  }

  private def isTriggerFor(varId : Int, t : ITerm) : Boolean = t match {
    case IFunApp(f, _) => f.partial && ContainsVariable(t, varId)
    case _             => false
  }

  private def isTriggerDefined(varId    : Int,
                               f        : IFormula,
                               polarity : Int) : Boolean = f match {
    case IQuantified(q, f2) if isEX(q, polarity) =>
      isTriggerDefined(varId + 1, f2, polarity)
    case ITrigger(trigs, body) =>
      trigs.exists((isTriggerFor(varId, _))) ||
      isTriggerDefined(varId, body, polarity)
    case INot(f2) =>
      isTriggerDefined(varId, f2, -polarity)
    case IBinFormula(IBinJunctor.Or, f1, f2) if polarity < 0 =>
      isTriggerDefined(varId, f1, polarity) ||
      isTriggerDefined(varId, f2, polarity)
    case IBinFormula(IBinJunctor.And, f1, f2) if polarity > 0 =>
      isTriggerDefined(varId, f1, polarity) ||
      isTriggerDefined(varId, f2, polarity)
    case Eq(_ : IFunApp, IVariable(`varId`)) |
         Eq(IVariable(`varId`), _ : IFunApp) if polarity > 0 =>
      true
    case _ =>
      false
  }

  override def preVisit(t : IExpression,
                        ctxt : Context[Unit]) : PreVisitResult = t match {
    case IQuantified(q, body) => {
      if (isEX(q, ctxt.polarity) &&
            ContainsVariable(body, 0) &&
            !isTriggerDefined(0, body, ctxt.polarity))
        throw FoundQuantifier
      super.preVisit(t, ctxt)
    }
    case _ =>
      super.preVisit(t, ctxt)
  }

  def postVisit(t : IExpression, ctxt : Context[Unit],
                subres : Seq[Unit]) : Unit = ()
}

////////////////////////////////////////////////////////////////////////////////

object QuantifierCollectingVisitor {
  private object FoundAll extends Exception

  def apply(f : IExpression) : Set[Quantifier] = {
    val visitor = new QuantifierCollectingVisitor
    try {
      visitor.visitWithoutResult(f, Context({}))
      visitor.foundQuantifiers.toSet
    } catch {
      case FoundAll => visitor.foundQuantifiers.toSet
    }
  }
}

/**
 * Visitor for collecting all quantifiers in a formula. The visitor
 * will not consider quantifiers expressing divisibility constraints.
 */
class QuantifierCollectingVisitor extends ContextAwareVisitor[Unit, Unit] {

  import QuantifierCollectingVisitor._
  import IExpression.{Sort, Divisibility, NonDivisibility}

  private val foundQuantifiers = new MHashSet[Quantifier]

  override def preVisit(t : IExpression,
                        ctxt : Context[Unit]) : PreVisitResult = t match {
    case Divisibility(_, _) | NonDivisibility(_, _) =>
      // divisibility, ignored
      super.preVisit(t, ctxt)

    case IQuantified(q, _) => {
      if (ctxt.polarity > 0) {
        foundQuantifiers += q
      } else if (ctxt.polarity < 0) {
        foundQuantifiers += q.dual
      } else {
        foundQuantifiers += Quantifier.ALL
        foundQuantifiers += Quantifier.EX
      }

      if (foundQuantifiers.size == 2)
        throw FoundAll

      super.preVisit(t, ctxt)
    }

    case _ =>
      super.preVisit(t, ctxt)
  }

  def postVisit(t : IExpression, ctxt : Context[Unit],
                subres : Seq[Unit]) : Unit = ()
}

////////////////////////////////////////////////////////////////////////////////

object Transform2Prenex {
  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : IFormula =
    applyHelp(f,
              Set(Quantifier.EX, Quantifier.ALL),
              QuantifierCountVisitor(f))

  def apply(f : IFormula,
            consideredQuantifiers : Set[Quantifier]) : IFormula =
    applyHelp(f,
              consideredQuantifiers,
              QuantifierCountVisitor(f, consideredQuantifiers))

  private def applyHelp(f : IFormula,
                        consideredQuantifiers : Set[Quantifier],
                        quantifierNum : Int) : IFormula =
    if (quantifierNum == 0) {
      f
    } else {
      val v = new Transform2Prenex(quantifierNum, consideredQuantifiers)
      val quantifierFree =
        v.visit(f, Context(List[IVariable]())).asInstanceOf[IFormula]
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, quantifierNum == v.quantifiersToAdd.size)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      IExpression.quanWithSorts(v.quantifiersToAdd.reverse, quantifierFree)
    }
}

/**
 * Turn a formula into prenex form.
 */
class Transform2Prenex private (finalQuantifierNum : Int,
                                consideredQuantifiers : Set[Quantifier])
      extends ContextAwareVisitor[List[IVariable], IExpression] {

  private val quantifiersToAdd = new ArrayBuffer[(Quantifier, Sort)]

  override def preVisit(t : IExpression,
                        context : Context[List[IVariable]])
                       : PreVisitResult = t match {
    case ISortedQuantified(q, sort, _) => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(Transform2Prenex.AC, context.polarity != 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val realQuan = if (context.polarity > 0) q else q.dual
      if (consideredQuantifiers contains realQuan) {
        val newVars =
          IVariable(finalQuantifierNum - quantifiersToAdd.size - 1,
                    sort) :: context.a
        quantifiersToAdd += ((realQuan, sort))
        super.preVisit(t, context(newVars))
      } else {
        // Don't look underneath this quantifier. We still have to substitute
        // variables in the right way
        ShortCutResult(
          VariableSubstVisitor(t,
            (context.a, finalQuantifierNum - context.a.size)))
      }
    }
    // Triggers will not make sense anymore after turning to prenex, so
    // currently we just drop them
    case ITrigger(_, f) =>
      TryAgain(f, context)
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
          v shiftedBy (finalQuantifierNum - context.a.size)
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

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor that is able to detect shared sub-expression (i.e., sub-expressions
 * with object identity) and replace them with abbreviations.
 */
object SubExprAbbreviator {
  private val AC = Debug.AC_INPUT_ABSY

  def apply(t : IExpression,
            abbreviator : IExpression => IExpression) : IExpression = {
    val exprOccurrences = new MHashMap[IExpression, Int]

    val countingVisitor = new Counter(exprOccurrences)
    countingVisitor.visitWithoutResult(t, ())

    val abbrevVisitor = new Abbreviator(exprOccurrences, abbreviator)

    abbrevVisitor.visit(t, ())
  }

  private class Counter(exprOccurrences : MHashMap[IExpression, Int])
          extends CollectingVisitor[Unit, Unit] {

    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      (exprOccurrences get t) match {
        case Some(num) => {
          exprOccurrences.put(t, num + 1)
          ShortCutResult(())
        }
        case None => {
          exprOccurrences.put(t, 1)
          KeepArg
        }
      }

    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }

  private class Abbreviator(exprOccurrences : MHashMap[IExpression, Int],
                            abbreviator : IExpression => IExpression)
          extends CollectingVisitor[Unit, IExpression] {
    private val abbrevs = new MHashMap[IExpression, IExpression]

    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      (abbrevs get t) match {
        case Some(newExpr) => {
          ShortCutResult(newExpr)
        }
        case None =>
          KeepArg
      }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = {
      val newT = t update subres
      if (exprOccurrences(t) > 1) {
        val abbrev = abbreviator(newT)
        if (abbrev eq newT) {
          newT
        } else {
          abbrevs.put(t, abbrev)
          abbrev
        }
      } else {
        newT
      }
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Visitor that checks whether the sorts of variables are consistent with
 * the sort of their binders.
 */
object VariableSortChecker
       extends CollectingVisitor[String, Set[IVariable]] {

  def apply(prefix : String, e : IExpression) : Unit =
    this.visit(e, prefix)

  def apply(prefix : String, es : Iterable[IExpression]) : Unit =
    for (e <- es)
      apply(prefix, e)

  def postVisit(t : IExpression,
                prefix : String,
                subres : Seq[Set[IVariable]]) : Set[IVariable] = {
    val bodyVars =
      subres match {
        case Seq() => Set[IVariable]()
        case sets  => sets reduceLeft (_ ++ _)
      }

    t match {
      case t : IVariable =>
        bodyVars + t
      case t : IVariableBinder => {
        val extraSorts =
          (for (v@ISortedVariable(0, s) <- bodyVars; if s != t.sort)
           yield v).toSeq
        if (!extraSorts.isEmpty)
          Console.err.println("Warning " + prefix + ": variables " +
                                (extraSorts mkString ", ") +
                                " occurring in " + t)
        for (t@IVariable(ind) <- bodyVars; if ind > 0) yield (t shiftedBy -1)
      }
      case _ =>
        bodyVars
    }
  }

}
