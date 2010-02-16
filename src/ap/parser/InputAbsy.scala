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
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.terfor.preds.Predicate
import ap.util.{Debug, Seqs}

/**
 * Abstract syntax for prover input. The language represented by the following
 * constructors is more general than the logic that the prover actually can
 * handle (e.g., there are also functions, equivalence, etc.). The idea is
 * that inputs first have to be normalised in some way so that the prover can
 * handle them.
 */
abstract class IExpression extends RandomAccessSeq[IExpression] {
  // by default, there are no subexpressions
  def apply(i : Int) : IExpression = throw new IndexOutOfBoundsException
  def length : Int = 0
  
  /**
   * Replace the subexpressions of this node with new expressions
   */
  def update(newSubExprs : Seq[IExpression]) : IExpression = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    ////////////////////////////////////////////////////////////////////////////
    this
  }
}

object IExpression {
  protected[parser] val AC = Debug.AC_INPUT_ABSY
  
  implicit def i(value : Int) : ITerm = IIntLit(value)
  implicit def i(value : IdealInt) : ITerm = IIntLit(value)
  implicit def i(c : ConstantTerm) : ITerm = IConstant(c)
  def v(index : Int) : IVariable = IVariable(index)

  implicit def i(value : Boolean) : IFormula = IBoolLit(value)
  implicit def toPredApplier(pred : Predicate) : ((ITerm*) => IFormula) =
    new Function1[Seq[ITerm], IFormula] {
      def apply(args : Seq[ITerm]) = IAtom(pred, args)
    }
  implicit def toFunApplier(fun : IFunction) : ((ITerm*) => ITerm) =
    new Function1[Seq[ITerm], ITerm] {
      def apply(args : Seq[ITerm]) = IFunApp(fun, args)
    }

  def ex(f : IFormula) = IQuantified(Quantifier.EX, f)
  def all(f : IFormula) = IQuantified(Quantifier.ALL, f)

  def quan(quans : Seq[Quantifier], f : IFormula) : IFormula =
    (quans :\ f)(IQuantified(_, _))

  def quan(quan : Quantifier,
           consts : Collection[ConstantTerm],
           f : IFormula) : IFormula = {
    val fWithShiftedVars = VariableShiftVisitor(f, 0, consts.size)
    val subst = Map() ++ (for ((c, i) <- consts.elements.zipWithIndex) yield (c, v(i)))
    val fWithSubstitutedConsts = ConstantSubstVisitor(fWithShiftedVars, subst)
    (consts :\ fWithSubstitutedConsts) ((c, f) => IQuantified(quan, f))
  }
  
  def connect(fors : Iterable[IFormula], op : IBinJunctor.Value) : IFormula =
    connect(fors.elements, op)

  def connect(fors : Iterator[IFormula], op : IBinJunctor.Value) : IFormula =
    if (fors.hasNext) {
      fors.reduceLeft(IBinFormula(op, _, _))
    } else op match {
      case IBinJunctor.And | IBinJunctor.Eqv => true
      case IBinJunctor.Or => false
    }
  
  // extract the value of constant terms
  object Const {
    def unapply(t : ITerm) : Option[IdealInt] = t match {
      case IIntLit(v) => Some(v)
      case ITimes(IdealInt.ZERO, _) => Some(IdealInt.ZERO)
      case ITimes(c, Const(v)) => Some(c * v)
      case IPlus(Const(v1), Const(v2)) => Some(v1 + v2)
      case _ => None
    }
  }

  // identify formulae that do not have direct subformulae
  object LeafFormula {
    def unapply(t : IExpression) : Option[IFormula] = t match {
      case t : IBoolLit => Some(t)
      case t : IAtom => Some(t)
      case t : IIntFormula => Some(t)
      case _ => None
    }
  }
  
  protected[parser] def toTermSeq(newExprs : Seq[IExpression],
                                  oldExprs : Seq[ITerm]) : Option[Seq[ITerm]] = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newExprs.length == oldExprs.length)
    ////////////////////////////////////////////////////////////////////////////
    if (oldExprs.length == 0) {
      None
    } else {
      val newArgs = new scala.collection.mutable.ArrayBuffer[ITerm]
      var changed = false
      for ((newE, oldE) <- newExprs.elements zip oldExprs.elements) {
        val newArg = newE.asInstanceOf[ITerm]
        if (!(newArg eq oldE)) changed = true
        newArgs += newArg
      }
      if (changed) Some(newArgs) else None
    }
  }
  
  def removePartName(t : IFormula) : IFormula = t match {
    case INamedPart(_, subFor) => subFor
    case _ => t
  }
}

//////////////////////////////////////////////////////////////////////////////

abstract class ITerm extends IExpression {
  def +(that : ITerm) : ITerm = IPlus(this, that)
  def *(coeff : IdealInt) : ITerm = ITimes(coeff, this)
  def *(that : ITerm) : ITerm = (this, that) match {
    case (IExpression.Const(c), t) => t * c
    case (t, IExpression.Const(c)) => t * c
    case _ => throw new IllegalArgumentException
  }
  def unary_- : ITerm = ITimes(IdealInt.MINUS_ONE, this)
  def -(that : ITerm) : ITerm = IPlus(this, -that)
  def ===(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.EqZero, this - that)
  def =/=(that : ITerm) : IFormula =
    !(this === that)
  def >=(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, this - that)
  def <=(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, that - this)
  def >(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, this - that + IIntLit(IdealInt.MINUS_ONE))
  def <(that : ITerm) : IFormula =
    IIntFormula(IIntRelation.GeqZero, that - this + IIntLit(IdealInt.MINUS_ONE))

  override def update(newSubExprs : Seq[IExpression]) : ITerm = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    ////////////////////////////////////////////////////////////////////////////
    this
  }
}

case class IIntLit(value : IdealInt) extends ITerm {
  override def toString = value.toString
}

case class IConstant(c : ConstantTerm) extends ITerm {
  override def toString = c.toString
}

case class IVariable(index : Int) extends ITerm {
  ////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, index >= 0)
  ////////////////////////////////////////////////////////////////////////////
  override def toString = "_" + index
}

case class ITimes(coeff : IdealInt, subterm : ITerm) extends ITerm {
  override def apply(i : Int) : ITerm = i match {
    case 0 => subterm
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1               
  
  override def update(newSubExprs : Seq[IExpression]) : ITimes = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    ////////////////////////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[ITerm]
    if (newsub eq subterm) this else ITimes(coeff, newsub)
  }

  override def toString = "" + coeff + " * " + subterm
}

case class IPlus(t1 : ITerm, t2 : ITerm) extends ITerm {
  override def apply(i : Int) : ITerm = i match {
    case 0 => t1
    case 1 => t2
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 2               

  override def update(newSubExprs : Seq[IExpression]) : IPlus = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 2)
    ////////////////////////////////////////////////////////////////////////////
    val newt1 = newSubExprs(0).asInstanceOf[ITerm]
    val newt2 = newSubExprs(1).asInstanceOf[ITerm]
    if ((newt1 eq t1) && (newt2 eq t2)) this else IPlus(newt1, newt2)
  }

  override def toString = "(" + t1 + " + " + t2 + ")"
}

/**
 * The AST on this level can also express uninterpreted functions
 */
class IFunction(val name : String, val arity : Int,
                val partial : Boolean, val relational : Boolean) {

  override def toString = name + "/" + arity +
                          (if (partial) "p" else "") +
                          (if (relational) "r" else "")

}

case class IFunApp(fun : IFunction, args : Seq[ITerm]) extends ITerm {
  ////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, fun.arity == args.length)
  ////////////////////////////////////////////////////////////////////////////  
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
  
  override def hashCode : Int =
    fun.hashCode + Seqs.computeHashCode(args, 17, 3)
  
  override def toString =
    fun.name + 
    (if (args.length > 0)
       "(" + (for (t <- args.elements) yield t.toString).mkString(", ") + ")"
     else
       "")
}

//////////////////////////////////////////////////////////////////////////////

abstract class IFormula extends IExpression {
  def &(that : IFormula) : IFormula = IBinFormula(IBinJunctor.And, this, that)
  def |(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Or, this, that)
  def <->(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Eqv, this, that)
  def </>(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Eqv, !this, that)
  def ->(that : IFormula) : IFormula = IBinFormula(IBinJunctor.Or, !this, that)
  def unary_! : IFormula = INot(this)  

  // binary operators that directly simplify expressions involving true/false
  
  def &&&(that : IFormula) : IFormula = (this, that) match {
    case (f@IBoolLit(false), _) => f
    case (_, f@IBoolLit(false)) => f
    case (IBoolLit(true), f) => f
    case (f, IBoolLit(true)) => f
    case _ => this & that
  }
    
  def |||(that : IFormula) : IFormula = (this, that) match {
    case (f@IBoolLit(true), _) => f
    case (_, f@IBoolLit(true)) => f
    case (IBoolLit(false), f) => f
    case (f, IBoolLit(false)) => f
    case _ => this | that
  }
  
  def -->(that : IFormula) : IFormula = (this, that) match {
    case (IBoolLit(false), _) => true
    case (_, f@IBoolLit(true)) => f
    case (IBoolLit(true), f) => f
    case (f, IBoolLit(false)) => !f
    case _ => this -> that
  }
  
  override def update(newSubExprs : Seq[IExpression]) : IFormula = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.isEmpty)
    ////////////////////////////////////////////////////////////////////////////
    this
  }
}

case class IBoolLit(value : Boolean) extends IFormula {
  override def toString = value.toString
}

case class INot(subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : INot = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    ////////////////////////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else INot(newsub)
  }
  
  override def toString = "!" + subformula
}

object IBinJunctor extends Enumeration {
  val And, Or, Eqv = Value
}

case class IBinFormula(j : IBinJunctor.Value,
                       f1 : IFormula, f2 : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => f1
    case 1 => f2
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 2

  override def update(newSubExprs : Seq[IExpression]) : IBinFormula = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 2)
    ////////////////////////////////////////////////////////////////////////////
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
}

case class IAtom(pred : Predicate, args : Seq[ITerm]) extends IFormula {
  ////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(IExpression.AC, pred.arity == args.length)
  ////////////////////////////////////////////////////////////////////////////  
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
  
  override def hashCode : Int =
    pred.hashCode + Seqs.computeHashCode(args, 17, 3)
  
  override def toString =
    pred.name + 
    (if (args.length > 0)
       "(" + (for (t <- args.elements) yield t.toString).mkString(", ") + ")"
     else
       "")
}

object IIntRelation extends Enumeration {
  val EqZero, GeqZero = Value
}

case class IIntFormula(rel : IIntRelation.Value, t : ITerm) extends IFormula {
  override def apply(i : Int) : ITerm = i match {
    case 0 => t
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : IIntFormula = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    ////////////////////////////////////////////////////////////////////////////
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
}

case class IQuantified(quan : Quantifier, subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1

  override def update(newSubExprs : Seq[IExpression]) : IQuantified = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    ////////////////////////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else IQuantified(quan, newsub)
  }

  override def toString = "" + quan + " " + subformula
}

case class ITrigger(patterns : Seq[ITerm], subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IExpression = 
    if (i == patterns.length) subformula else patterns(i)
  override def length : Int = patterns.length + 1

  override def update(newSubExprs : Seq[IExpression]) : ITrigger = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length > 0)
    ////////////////////////////////////////////////////////////////////////////
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
}

object PartName {
   // the distinguished name used for unnamed formula parts
  val NO_NAME = new PartName ("NoName")
}

class PartName(override val toString : String)

case class INamedPart(name : PartName, subformula : IFormula) extends IFormula {
  override def apply(i : Int) : IFormula = i match {
    case 0 => subformula
    case _ => throw new IndexOutOfBoundsException
  }
  override def length : Int = 1
  
  override def update(newSubExprs : Seq[IExpression]) : INamedPart = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IExpression.AC, newSubExprs.length == 1)
    ////////////////////////////////////////////////////////////////////////////
    val newsub = newSubExprs(0).asInstanceOf[IFormula]
    if (newsub eq subformula) this else INamedPart(name, newsub)
  }

  override def toString = "\\part[" + name + "] " + subformula 
}

case class IInterpolantSpec(left : List[PartName], right : List[PartName])