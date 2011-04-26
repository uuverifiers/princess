/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.Signature
import ap.basetypes.IdealInt
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the CSIsat format
 * 
 * Currently, functions are not handled in this class
 */
object CSIsatLineariser {

  def apply(formula : IFormula) = {
    AbsyPrinter.visit(formula, PrintContext(List(), ""))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private case class PrintContext(vars : List[String], parentOp : String) {
    def pushVar(name : String) = PrintContext(name :: vars, parentOp)
    def setParentOp(op : String) = PrintContext(vars, op)
  }
  
  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    
    private def allButLast(ctxt : PrintContext, op : String, arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
                List(ctxt setParentOp ""))
    }
    
    private def noParentOp(ctxt : PrintContext) = UniSubArgs(ctxt setParentOp "")
    
    override def preVisit(t : IExpression,
                          ctxt : PrintContext) : PreVisitResult = t match {
      // Terms
      case IConstant(c) => {
        print(c.name)
        noParentOp(ctxt)
      }
      case IIntLit(value) => {
        print(value)
        noParentOp(ctxt)
      }
      case IPlus(_, _) => {
        print("(")
        allButLast(ctxt, " + ", 2)
      }
      case ITimes(coeff, _) => {
        print(coeff + " * (")
        UniSubArgs(ctxt setParentOp "")
      }
      case IVariable(index) => {
        print(ctxt vars index)
        noParentOp(ctxt)
      }
        
      // Formulae
      case IAtom(pred, _) => {
        print(pred.name)
        if (pred.arity > 0)
          print("(")
        allButLast(ctxt, ", ", pred.arity)
      }
      case IBinFormula(junctor, _, _) => {
        print("(")
        allButLast(ctxt,
                   (junctor match {
                     case IBinJunctor.And => " & "
                     case IBinJunctor.Or => " | "
                     case IBinJunctor.Eqv => " <-> "
                    }),
                   2)
      }
      case IBoolLit(value) => {
        print(value)
        noParentOp(ctxt)
      }
      case IIntFormula(rel, _) => {
        UniSubArgs(ctxt setParentOp "")
      }
      case INot(_) => {
        print("not ")
        UniSubArgs(ctxt setParentOp "")
      }
      case IQuantified(quan, _) => {
        val varName = "boundVar" + ctxt.vars.size
        print(quan match {
          case Quantifier.ALL => "\\forall"
          case Quantifier.EX => "\\exists"
        })
        print(" int " + varName + "; ")
        UniSubArgs(ctxt pushVar varName)
      }
      case INamedPart(name, _) => {
/*        if (name != PartName.NO_NAME)
          print("\\part[" + name + "] ") */
        print("(")
        UniSubArgs(ctxt setParentOp "")
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit = {
      t match {
        case IPlus(_, _) | ITimes(_, _) | IBinFormula(_, _, _) => print(")")
        
        case IAtom(pred, _) if (pred.arity > 0) => print(")")
        
        case IIntFormula(rel, _) =>
          print(" " + (rel match {
                         case IIntRelation.EqZero => "="
                         case IIntRelation.GeqZero => ">="
                       }) + " 0")
        
        case INamedPart(_, _) => println(")")
          
        case _ => // no closing paren
      }
      print(ctxt.parentOp)
    }
  
  }
  
}
