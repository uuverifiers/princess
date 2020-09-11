/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2020 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.DialogUtil
import ap.basetypes.IdealInt
import ap.terfor.preds.Predicate
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.types.Sort
import ap.theories.ModuloArithmetic
import ap.util.Seqs

import java.io.PrintStream

object PrettyScalaLineariser {

  def apply(functionNames : PartialFunction[IFunction, String]) =
    new PrettyScalaLineariser(functionNames)

  def printSort(sort : Sort) : Unit = sort match {
    case Sort.Integer =>
      print("Sort.Integer")
    case Sort.Nat =>
      print("Sort.Nat")
    case Sort.Bool =>
      print("Sort.Bool")
    case Sort.MultipleValueBool =>
      print("Sort.MultipleValueBool")
    case Sort.Interval(lower, upper) =>
      print("Sort.Interval(" +
            (for (l <- lower) yield int2String(l)) + ", " +
            (for (u <- upper) yield int2String(u)) + ")")
    case ModuloArithmetic.ModSort(lower, upper) =>
      print("ap.theories.ModuloArithmetic.ModSort(" +
            int2String(lower) + ", " + int2String(upper) + ")")
  }

  def sort2String(sort : Sort) : String =
    DialogUtil asString { printSort(sort) }

  private def int2String(value : IdealInt) : String = {
    val intValue = value.intValue
    if (value == IdealInt(intValue))
      "" + intValue
    else
      "IdealInt(\"" + value + "\")"
  }

}

/**
 * Class for printing <code>IExpression</code>s in pretty Scala syntax
 */
class PrettyScalaLineariser private (
               functionNames : PartialFunction[IFunction, String]) {

  import PrettyScalaLineariser.{int2String, printSort}

  def apply(e : IExpression) =
    AbsyPrinter.visit(e, PrintContext(List(), "", true))
  
  //////////////////////////////////////////////////////////////////////////////
  
  private case class PrintContext(vars : List[String], parentOp : String,
                                  requireWrapping : Boolean) {
    def pushVar(name : String)   = PrintContext(name :: vars, parentOp, requireWrapping)
    def setOpNoWrap(op : String) = PrintContext(vars, op, false)
    def setOpWrap(op : String)   = PrintContext(vars, op, true)
    def setWrapping(b : Boolean) = PrintContext(vars, parentOp, b)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    
    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setOpNoWrap op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
                List(ctxt setOpNoWrap lastOp))
    }
    
    private def noOp(ctxt : PrintContext) = UniSubArgs(ctxt setOpNoWrap "")
    
    private def shortCut(ctxt : PrintContext) = {
      print(ctxt.parentOp)
      ShortCutResult(())
    }
    
    private object AtomicTerm {
      def unapply(t : IExpression) : Option[ITerm] = t match {
        case t : IConstant => Some(t)
        case t : IVariable => Some(t)
        case t : IIntLit   => Some(t)
        case _ => None
      }
    }

    private def atomicTerm(t : ITerm,
                           ctxt : PrintContext) : String =
      if (ctxt.requireWrapping)
        atomicTermWrap(t, ctxt)
      else
        atomicTermNoWrap(t, ctxt)

    private def atomicTermWrap(t : ITerm,
                               ctxt : PrintContext) : String = t match {
      case IConstant(c)     => c.name
      case IVariable(index) => ctxt vars index
      case IIntLit(value)   => "IIntLit(IdealInt(\"" + int2String(value) + "\"))"
    }

    private def atomicTermNoWrap(t : ITerm,
                                 ctxt : PrintContext) : String = t match {
      case IConstant(c)     => c.name
      case IVariable(index) => ctxt vars index
      case IIntLit(value)   => int2String(value)
    }

    private def relation(rel : IIntRelation.Value) = rel match {
      case IIntRelation.EqZero => "==="
      case IIntRelation.GeqZero => ">="
    }

    private def negRelation(rel : IIntRelation.Value) = rel match {
      case IIntRelation.EqZero => "==="
      case IIntRelation.GeqZero => "<="
    }

    override def preVisit(t : IExpression,
                          ctxt : PrintContext) : PreVisitResult = {
      t match {
        // Terms
        case AtomicTerm(t) => {
          print(atomicTerm(t, ctxt))
          noOp(ctxt)
        }

        case IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t))) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (
                       " - " + atomicTermNoWrap(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (
                       " - " + atomicTermNoWrap(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IPlus(s, ITimes(coeff, AtomicTerm(t))) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (
                       " - (" + atomicTermWrap(t, ctxt) + "*" + int2String(coeff.abs) +
                       "))" + ctxt.parentOp))
        }
        case IPlus(ITimes(coeff, AtomicTerm(t)), s) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (
                       " - (" + atomicTermWrap(t, ctxt) + "*" + int2String(coeff.abs) +
                       "))" + ctxt.parentOp))
        }

        case IPlus(_, _) => {
          print("(")
          SubArgs(List(ctxt setOpWrap " + ", ctxt setOpNoWrap ")"))
        }

        case ITimes(coeff, _) => {
          print("(")
          UniSubArgs(ctxt setOpWrap (" * " + int2String(coeff) + ")"))
        }
      
        case IFunApp(fun, _) => {
          print(functionNames.applyOrElse(fun, (f : IFunction) => f.name))
          print("(")
          allButLast(ctxt, ", ", ")", fun.arity)
        }
        
        case _ : ITermITE => {
          print("ITermITE(")
          allButLast(ctxt, ", ", ")", 3)
        }

        case ISortedEpsilon(sort, _) => {
          val varName = "v" + ctxt.vars.size
          printSort(sort)
          print(".eps(")
          print(varName + " => ")
          UniSubArgs(ctxt pushVar varName setOpNoWrap ")")
        }

        // Formulae
        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt, ", ", ")", pred.arity)
          } else {
            noOp(ctxt)
          }
        }
        
        case IBinFormula(junctor, left, right) => {
          print("(")
          val op = junctor match {
            case IBinJunctor.And => " & "
            case IBinJunctor.Or => " | "
            case IBinJunctor.Eqv => " <=> "
          }
          SubArgs(List(ctxt setOpWrap op, ctxt setOpNoWrap ")"))
        }
        
        case IBoolLit(value) => {
          if (ctxt.requireWrapping)
            print("IBoolLit(" + value + ")")
          else
            print(value)
          noOp(ctxt)
        }
      
        case IIntFormula(rel, ITimes(IdealInt.MINUS_ONE, t)) => {
          print("(")
          TryAgain(t, ctxt setOpWrap (" " + negRelation(rel) + " 0)" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " +
                                        atomicTermNoWrap(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " +
                                        atomicTermNoWrap(t, ctxt) + ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(AtomicTerm(t), ITimes(IdealInt.MINUS_ONE, s))) => {
          print("(" + atomicTermWrap(t, ctxt) + " " + relation(rel) + " ")
          TryAgain(s, ctxt setOpNoWrap (")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, s), AtomicTerm(t))) => {
          print("(" + atomicTermWrap(t, ctxt) + " " + relation(rel) + " ")
          TryAgain(s, ctxt setOpNoWrap (")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(ITimes(coeff, AtomicTerm(t)), s)) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " +
                                      atomicTermWrap(t, ctxt) + "*" + int2String(coeff.abs) +
                                      ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(s, ITimes(coeff, AtomicTerm(t)))) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " +
                                      atomicTermWrap(t, ctxt) + "*" + int2String(coeff.abs) +
                                      ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(IIntLit(value), s)) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " + int2String(-value) +
                                      ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(s, IIntLit(value))) => {
          print("(")
          TryAgain(s, ctxt setOpWrap (" " + relation(rel) + " " + int2String(-value) +
                                      ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, _) => {
          print("(")
          UniSubArgs(ctxt setOpWrap (" " + relation(rel) + " 0)"))
        }
      
        case INot(INot(subF)) => {
          TryAgain(subF, ctxt)
        }
        case INot(_) => {
          print("!")
          UniSubArgs(ctxt setOpWrap "")
        }

        case ISortedQuantified(quan, sort, _) => {
          val varName = "v" + ctxt.vars.size
          printSort(sort)
          print(".")
          print(quan match {
            case Quantifier.ALL => "all("
            case Quantifier.EX => "ex("
          })
          print(varName + " => ")
          UniSubArgs(ctxt pushVar varName setOpNoWrap ")")
        }

        case _ : IFormulaITE => {
          print("ITermITE(")
          SubArgs(List(ctxt setOpNoWrap ", ",
                       ctxt setOpNoWrap ", ",
                       ctxt setOpNoWrap ")"))
        }

        case INamedPart(name, _) => {
          print("INamedPart(")
          name match {
            case PartName.NO_NAME => print("PartName.NO_NAME")
            case _ => print(name)
          }
          print(", ")
          UniSubArgs(ctxt setOpNoWrap ")")
        }

        case ITrigger(trigs, _) => {
          print("ITrigger(List(")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
                     yield (ctxt setOpNoWrap ", ")) ++
                  List(ctxt setOpNoWrap "), ", ctxt setOpNoWrap ")"))
        }
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)
  
  }
  
}
