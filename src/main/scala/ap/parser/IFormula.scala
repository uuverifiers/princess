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

import ap.basetypes.IdealInt
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.terfor.preds.Predicate
import ap.types.Sort
import ap.util.{Debug, Seqs}

import scala.collection.mutable.ArrayBuffer
import scala.runtime.ScalaRunTime

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
 * Equation between two terms.
 */
case class IEquation(left : ITerm, right : ITerm) extends IFormula {
  override def apply(i : Int) : ITerm = i match {
    case 0 => left
    case 1 => right
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 2

  override def update(newSubExprs : Seq[IExpression]) : IEquation = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newLeft  = newSubExprs(0).asInstanceOf[ITerm]
    val newRight = newSubExprs(1).asInstanceOf[ITerm]
    if ((newLeft eq left) && (newRight eq right))
      this
    else
      IEquation(newLeft, newRight)
  }

  override def toString =
    "(" + left + " = " + right + ")"

  override val hashCode : Int = ScalaRunTime._hashCode(this)
}

/**
 * Integer relation operators.
 */
object IIntRelation extends Enumeration {
  val EqZero, GeqZero = Value
}

/**
 * Integer equation or inequality.
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
 * with de Bruijn index 0 and any sort.
 */
object IQuantified {
  def apply(quan : Quantifier, subformula : IFormula) : IQuantified =
    ISortedQuantified(quan, Sort.Integer, subformula)
  def apply(quan : Quantifier,
            sort : Sort, subformula : IFormula) : IQuantified =
    ISortedQuantified(quan, sort, subformula)

  def unapply(f : IQuantified) : Option[(Quantifier, IFormula)] = f match {
    case ISortedQuantified(quan, _, subformula) => Some((quan, subformula))
    case _                                      => None
  }
}

/**
 * Application of a quantifier to a formula containing a free variable
 * with de Bruijn index 0 and the given sort.
 */
abstract class IQuantified extends IFormula with IVariableBinder {
  /**
   * The quantifier.
   */
  def quan : Quantifier

  /**
   * The sort of the bound variable.
   */
  def sort : Sort

  /**
   * The body of the quantified formula.
   */
  def subformula : IFormula
}

/**
 * Application of a quantifier to a formula containing a free variable
 * with de Bruijn index 0 and the given sort.
 */
case class ISortedQuantified(quan : Quantifier,
                             sort : Sort,
                             subformula : IFormula) extends IQuantified {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : ISortedQuantified = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else ISortedQuantified(quan, sort, newsub)
  }

  override def toString =
    "" + quan +
    (if (sort == Sort.Integer) " " else (" " + sort.toString + ". ")) +
    subformula

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
        case _ : IVariableBinder => ShortCutResult(false)
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
case class ITrigger(patterns : Seq[ITerm],
                    subformula : IFormula) extends IFormula {
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
  val NO_NAME         = new PartName ("NoName")
  /** The distinguished name used for function axioms. */
  val FUNCTION_AXIOMS = new PartName ("FunctionAxioms")
  /** The distinguished name used for function axioms. */
  val THEORY_AXIOMS   = new PartName ("TheoryAxioms")

  val predefNames : Seq[PartName] =
    List(NO_NAME, FUNCTION_AXIOMS, THEORY_AXIOMS)
  val predefNamesSet : Set[PartName] =
    predefNames.toSet
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
