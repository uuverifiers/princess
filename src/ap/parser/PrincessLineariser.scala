/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010,2011 Philipp Ruemmer <ph_r@gmx.net>
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
 * Class for printing <code>IFormula</code>s in the Princess format
 * 
 * Currently, functions are not handled in this class
 */
object PrincessLineariser {

  def apply(formula : IFormula, signature : Signature) = {
    val order = signature.order

    println("// Generated by Princess (http://www.philipp.ruemmer.org/princess.shtml) }")

    // declare the various kinds of constants
    for ((name, consts) <- List(("universalConstants", signature.universalConstants),
    		                    ("existentialConstants", signature.existentialConstants),
                                ("functions", signature.nullaryFunctions)))
      if (!consts.isEmpty) {
        println("\\" + name + " {")
        for (c <- consts)
          println("int " + c.name + ";")
        println("}")
      }
    
    // declare the required predicates
    if (!order.orderedPredicates.isEmpty) {
      println("\\predicates {")
      for (pred <- order.orderedPredicates) {
        print(pred.name)
        if (pred.arity > 0) {
          print("(")
          print((for (_ <- List.range(0, pred.arity)) yield "int") mkString ", ")
          print(")")
        }
        println(";")
      }
      println("}")
    }
    
    println("\\problem {")
    printExpression(formula)
    println
    println("}")
  }
  
  def printExpression(e : IExpression) =
    AbsyPrinter.visit(e, PrintContext(List(), "", 0))
  
  //////////////////////////////////////////////////////////////////////////////
  
  private case class PrintContext(vars : List[String],
                                  parentOp : String,
                                  outerPrec : Int) {
    def pushVar(name : String)          = PrintContext(name :: vars, parentOp, outerPrec)
    def setParentOp(op : String)        = PrintContext(vars, op, outerPrec)
    def setOpPrec(op : String, l : Int) = PrintContext(vars, op, l)
    def setPrecLevel(l : Int)           = PrintContext(vars, parentOp, l)
  }
  
  private object AtomicTerm {
    def unapply(t : IExpression) : Option[ITerm] = t match {
      case t : IConstant => Some(t)
      case t : IVariable => Some(t)
      case _ => None
    }
  }
    
  private def atomicTerm(t : ITerm,
                         ctxt : PrintContext) : String = t match {
    case IConstant(c)     => c.name
    case IVariable(index) => ctxt vars index
  }
    
  private def relation(rel : IIntRelation.Value) = rel match {
    case IIntRelation.EqZero => "="
    case IIntRelation.GeqZero => ">="
  }

  private def precLevel(e : IExpression) : Int = e match {
    case IBinFormula(IBinJunctor.Eqv, _, _)             => 0
    case IBinFormula(IBinJunctor.Or, _, _)              => 0
    case IBinFormula(IBinJunctor.And, _, _)             => 0
    case _ : ITermITE | _ : IFormulaITE                 => 1
    case _ : INot | _ : IQuantified | _ : INamedPart |
         _ : ITrigger                                   => 3
    case _ : IIntFormula                                => 4
    case _ : IPlus                                      => 5
    case _ : ITimes                                     => 6
    case _ : ITerm | _ : IBoolLit | _ : IAtom           => 10
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
    
    override def preVisit(t : IExpression,
                          oldCtxt : PrintContext) : PreVisitResult = {
      // first use the precedence level of operators to determine whether we
      // have to insert parentheses
      
      val newPrecLevel = precLevel(t)
      
      val ctxt =
        if (newPrecLevel > oldCtxt.outerPrec) {
          oldCtxt setPrecLevel newPrecLevel
        } else if (newPrecLevel < oldCtxt.outerPrec) {
          // then we need parentheses
          print("(")
          return TryAgain(t, oldCtxt.setOpPrec(")" + oldCtxt.parentOp, newPrecLevel))
        } else {
          oldCtxt
        }
                            
      t match {
        // Terms
        case IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t))) => {
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IPlus(s, ITimes(coeff, AtomicTerm(t))) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" - " + coeff.abs + "*" + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s) => {
          TryAgain(s, ctxt setParentOp (" - " + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IPlus(ITimes(coeff, AtomicTerm(t)), s) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" - " + coeff.abs + "*" + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
      
        case AtomicTerm(t) => {
          print(atomicTerm(t, ctxt))
          noParentOp(ctxt)
        }
        case IIntLit(value) => {
          print(value)
          noParentOp(ctxt)
        }
        case IPlus(_, _) => {
          allButLast(ctxt, " + ", "", 2)
        }

        case ITimes(coeff, _) => {
          print(coeff + " * ")
          noParentOp(ctxt)
        }
      
        case IFunApp(fun, _) => {
          print(fun.name)
          print("(")
          allButLast(ctxt setPrecLevel 0, ", ", ")", fun.arity)
        }
        
        case _ : ITermITE | _ : IFormulaITE => {
          print("\\if (")
          SubArgs(List(ctxt setParentOp ") \\ then (",
                       ctxt setParentOp ") \\ else (",
                       ctxt setParentOp ")"))
        }

        // Formulae
        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            allButLast(ctxt setPrecLevel 0, ", ", ")", pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }
        
        case IBinFormula(junctor, left, right) => {
          val op = junctor match {
            case IBinJunctor.And => " & "
            case IBinJunctor.Or => " | "
            case IBinJunctor.Eqv => " <-> "
          }
          
          val newLeftCtxt = left match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec(op, 1)
            case _ =>
              ctxt setParentOp op
          }
          val newRightCtxt = right match {
            case IBinFormula(j2, _, _) if (junctor != j2) =>
              ctxt.setOpPrec("", 1)
            case _ =>
              ctxt setParentOp ""
          }
          
          SubArgs(List(newLeftCtxt, newRightCtxt))
        }
        
        case IBoolLit(value) => {
          print(value)
          noParentOp(ctxt)
        }
      
        case IIntFormula(rel, ITimes(IdealInt.MINUS_ONE, t)) => {
          print("0 " + relation(rel) + " ")
          TryAgain(t, ctxt)
        }
        case IIntFormula(rel, IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(s, ITimes(coeff, AtomicTerm(t)))) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " + coeff.abs + "*" +
                                        atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " +
                                        atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(ITimes(coeff, AtomicTerm(t)), s)) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " + coeff.abs + "*" +
                                        atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(rel, IPlus(IIntLit(value), s)) => {
          TryAgain(s, ctxt setParentOp (" " + relation(rel) + " " + (-value) +
                                        ctxt.parentOp))
        }
      
        case IIntFormula(rel, _) => {
          UniSubArgs(ctxt setParentOp (" " + relation(rel) + " 0"))
        }
      
        case INot(subF) => {
          print("!")
          noParentOp(
            subF match {
              case _ : IIntFormula =>
                ctxt setPrecLevel 10
              case _ =>
                ctxt
            })
        }
        case IQuantified(quan, _) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => "\\forall"
            case Quantifier.EX => "\\exists"
          })
          print(" int " + varName + "; ")
          noParentOp(ctxt pushVar varName)
        }
        case INamedPart(name, _) => {
          if (name != PartName.NO_NAME)
            print("\\part[" + name + "] ")
          noParentOp(ctxt)
        }
        case ITrigger(trigs, _) => {
          print("{")
          SubArgs((for (_ <- 0 until (trigs.size - 1))
                     yield (ctxt setParentOp ", ")) ++
                  List(ctxt setParentOp "} ", ctxt setParentOp ""))
        }
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)
  
  }
  
}
