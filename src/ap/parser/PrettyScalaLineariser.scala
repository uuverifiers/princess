/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.basetypes.IdealInt
import ap.terfor.preds.Predicate
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs

import java.io.PrintStream

object PrettyScalaLineariser {
  def apply(functionNames : Map[IFunction, String]) =
    new PrettyScalaLineariser(functionNames)
}

/**
 * Class for printing <code>IExpression</code>s in pretty Scala syntax
 */
class PrettyScalaLineariser private (functionNames : Map[IFunction, String]) {

  def apply(e : IExpression) =
    AbsyPrinter.visit(e, PrintContext(List(), ""))
  
  //////////////////////////////////////////////////////////////////////////////
  
  private case class PrintContext(vars : List[String], parentOp : String) {
    def pushVar(name : String)          = PrintContext(name :: vars, parentOp)
    def setParentOp(op : String)        = PrintContext(vars, op)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    
    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
                List(ctxt setParentOp lastOp))
    }
    
    private def noParentOp(ctxt : PrintContext) = UniSubArgs(ctxt setParentOp "")
    
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
                           ctxt : PrintContext) : String = t match {
      case IConstant(c)     => c.name
      case IVariable(index) => ctxt vars index
      case IIntLit(value)   => "i(" + int2String(value) + ")"
    }

    private def int2String(value : IdealInt) : String = {
      val intValue = value.intValue
      if (value == IdealInt(intValue))
        "" + intValue
      else
        "IdealInt(\"" + value + "\")"
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
          noParentOp(ctxt)
        }

        case IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t))) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IPlus(s, ITimes(coeff, AtomicTerm(t))) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + "*" + int2String(coeff.abs) +
                                        ")" + ctxt.parentOp))
        }
        case IPlus(ITimes(coeff, AtomicTerm(t)), s) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + "*" + int2String(coeff.abs) +
                                        ")" + ctxt.parentOp))
        }

        case IPlus(_, _) => {
          print("(")
          allButLast(ctxt, " + ", ")", 2)
        }

        case ITimes(coeff, _) => {
          print("(")
          UniSubArgs(ctxt setParentOp (" * " + int2String(coeff) + ")"))
        }
      
        case IFunApp(fun, _) => {
          print(functionNames.getOrElse(fun, fun.name))
          print("(")
          allButLast(ctxt, ", ", ")", fun.arity)
        }
        
        case _ : ITermITE => {
          print("ITermITE(")
          SubArgs(List(ctxt setParentOp ", ",
                       ctxt setParentOp ", ",
                       ctxt setParentOp ")"))
        }

        case IEpsilon(_) => {
          val varName = "v" + ctxt.vars.size
          print("eps(")
          print(varName + " => ")
          UniSubArgs(ctxt pushVar varName setParentOp ")")
        }

        // Formulae
        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt, ", ", ")", pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }
        
        case IBinFormula(junctor, left, right) => {
          print("(")
          val op = junctor match {
            case IBinJunctor.And => " & "
            case IBinJunctor.Or => " | "
            case IBinJunctor.Eqv => " <=> "
          }
          allButLast(ctxt, op, ")", 2)
        }
        
        case IBoolLit(value) => {
          print("i(" + value + ")")
          noParentOp(ctxt)
        }
      
        case IIntFormula(rel, ITimes(IdealInt.MINUS_ONE, t)) => {
          print("(")
          TryAgain(t, ctxt setParentOp (" " + negRelation(rel) + " 0)" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(AtomicTerm(t), ITimes(IdealInt.MINUS_ONE, s))) => {
          print("(" + atomicTerm(t, ctxt) + " " + relation(rel) + " ")
          TryAgain(s, ctxt setParentOp (")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, s), AtomicTerm(t))) => {
          print("(" + atomicTerm(t, ctxt) + " " + relation(rel) + " ")
          TryAgain(s, ctxt setParentOp (")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(ITimes(coeff, AtomicTerm(t)), s)) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + "*" + int2String(coeff.abs) +
                                        ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(s, ITimes(coeff, AtomicTerm(t)))) if (coeff.signum < 0) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + "*" + int2String(coeff.abs) +
                                        ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, IPlus(IIntLit(value), s)) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " + int2String(-value) +
                                        ")" + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(s, IIntLit(value))) => {
          print("(")
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " + int2String(-value) +
                                        ")" + ctxt.parentOp))
        }

        case IIntFormula(rel, _) => {
          print("(")
          UniSubArgs(ctxt setParentOp (" " + relation(rel) + " 0)"))
        }
      
        case INot(INot(subF)) => {
          TryAgain(subF, ctxt)
        }
        case INot(_) => {
          print("!")
          noParentOp(ctxt)
        }

        case IQuantified(quan, _) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => "all("
            case Quantifier.EX => "ex("
          })
          print(varName + " => ")
          UniSubArgs(ctxt pushVar varName setParentOp ")")
        }

        case _ : IFormulaITE => {
          print("ITermITE(")
          SubArgs(List(ctxt setParentOp ", ",
                       ctxt setParentOp ", ",
                       ctxt setParentOp ")"))
        }

        case INamedPart(name, _) => {
          print("INamedPart(")
          name match {
            case PartName.NO_NAME => print("PartName.NO_NAME")
            case _ => print(name)
          }
          print(", ")
          UniSubArgs(ctxt setParentOp ")")
        }

        case ITrigger(trigs, _) => {
          print("ITrigger(List(")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
                     yield (ctxt setParentOp ", ")) ++
                  List(ctxt setParentOp "), ", ctxt setParentOp ")"))
        }
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)
  
  }
  
}
