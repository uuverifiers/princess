/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010,2011 Philipp Ruemmer <ph_r@gmx.net>
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
	assert (pred.arity == 0)         // we do not handle positive-arity predicates
        print("(" + pred.name + " > 0)") // dump Boolean variable "q" everywhere as "q > 0"
        noParentOp(ctxt)
      }
      case IBinFormula(junctor, _, _) => {
        print("(")
        allButLast(ctxt,
                   (junctor match {
                     case IBinJunctor.And => " & "
                     case IBinJunctor.Or  => " | "
                     case IBinJunctor.Eqv => " <-> "
                    }),
                   2)
      }
      case IBoolLit(value) => {
	if (value)
	  print("(x = x)") // "true"
	else
	  print("(x > x)") // "false"
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
/*      if (name != PartName.NO_NAME)
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
