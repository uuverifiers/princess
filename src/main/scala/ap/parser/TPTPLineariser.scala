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

package ap.parser

import ap._
import ap.basetypes.IdealInt
import ap.theories.{BitShiftMultiplication, GroebnerMultiplication}
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet}

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the TPTP format
 */
object TPTPLineariser {
  def apply(formula : IFormula, benchmarkName : String) : Unit = {
    val lineariser = new TPTPLineariser(benchmarkName)
   
    lineariser.open
    lineariser.declareSymbols(formula)
    lineariser.printConjecture("conj", formula)
    lineariser.close
  }
}

/**
 * Class for printing <code>IFormula</code>s in the TPTP format
 */
class TPTPLineariser(benchmarkName : String) {

  //////////////////////////////////////////////////////////////////////////////

  private val seenSymbols = new MHashSet[AnyRef]

  private object DeclarationVisitor extends CollectingVisitor[Unit, Unit] {
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = t match {
      case IConstant(c) if (!(seenSymbols contains c)) => {
        seenSymbols += c
        val name = "" + c
        println("tff(" + name + "_type, type, (")
        println("    " + name + ": $int)).")
        KeepArg
      }
      case IFunApp(f, _) if (!(seenSymbols contains f) &&
                             f != GroebnerMultiplication.mul &&
                             f != BitShiftMultiplication.mul) => {
        seenSymbols += f
        val name = "" + f
        println("tff(" + name + "_type, type, (")
        print("    " + name + ": ")
        f.arity match {
          case 0 => // nothing
          case 1 => print("$int > ")
          case n => print("( " + (for (_ <- 0 until n) yield "$int").mkString(" * ")
                          + " ) > ")
        }
        println("$int)).")
        KeepArg
      }
      case IAtom(p, _) if (!(seenSymbols contains p)) => {
        seenSymbols += p
        val name = "" + p
        println("tff(" + name + "_type, type, (")
        print("    " + name + ": ")
        p.arity match {
          case 0 => // nothing
          case 1 => print("$int > ")
          case n => print("( " + (for (_ <- 0 until n) yield "$int").mkString(" * ")
                          + " ) > ")
        }
        println("$o)).")
        KeepArg
      }
      case _ => KeepArg
    }
    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[Unit]) : Unit = {}
  }

  //////////////////////////////////////////////////////////////////////////////

  def open {
    println("%------------------------------------------------------------------------------")
    println("% File     : " + benchmarkName)
    println("% Domain   : <The domain of the problem, from the TPTP domains>")
    println("% Problem  : <A one line description of the problem>")
    println("% Version  : <If this is a different form of an existing problem, why it is ")
    println("%             different>")
    println("% English  : <A full description of the problem>")
    println("")
    println("% Refs     : <Relevant references>")
    println("% Source   : <The Ref where the formulae originate from>")
    println("% Names    : <The name(s) of this problem in the literature>")
    println("")
    println("% Status   : <A value from the SZS ontology>")
    println("% Rating   : <Don't worry about this one - we'll do it automatically>")
    println("% Syntax   : <Don't worry about this one - we'll do it automatically>")
    println("% SPC      : <Don't worry about this one - we'll do it automatically>")
    println("")
    println("% Comments : <Anything else that might be useful>")
    println("%            Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("%------------------------------------------------------------------------------")
  }

  def declareSymbols(f : IFormula) : Unit =
    DeclarationVisitor.visitWithoutResult(f, ())

  def printConjecture(name : String, f : IFormula) {
    println("tff(" + name + ", conjecture, (")
    printFormula(f)
    println(")).")
  }
  
  def printFormula(formula : IFormula) =
    AbsyPrinter.visit(formula, PrintContext(List(), "", 0))
  
  def printTerm(t : ITerm) =
    AbsyPrinter.visit(t, PrintContext(List(), "", 0))
  
  def close {
    println("%------------------------------------------------------------------------------")
  }
  
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
      case t : IIntLit   => Some(t)
      case _ => None
    }
  }
    
  private def atomicTerm(t : ITerm,
                         ctxt : PrintContext) : String = t match {
    case IConstant(c)     => c.name
    case IVariable(index) => ctxt vars index
    case IIntLit(value)   => "" + value
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
    case _ : IEquation                                  => 2
    case _ : INot | _ : IQuantified | _ : INamedPart |
         _ : ITrigger | _ : IEpsilon                    => 3
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

    private def prefixNotation(ctxt : PrintContext, arity : Int) =    
      allButLast(ctxt setPrecLevel 0, ", ", ")", arity)

    private def addClosingParen(ctxt : PrintContext) =
      addClosingString(ctxt, ")")

    private def addClosingString(ctxt : PrintContext, str : String) =
      ctxt setPrecLevel 0 setParentOp (str + ctxt.parentOp)

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
          print("$difference(")
          TryAgain(s, addClosingString(ctxt, ", " + atomicTerm(t, ctxt) + ")"))
        }
        case IPlus(s, ITimes(coeff, AtomicTerm(t))) if (coeff.signum < 0) => {
          print("$difference(")
          TryAgain(
            s,
            addClosingString(
              ctxt,
              ", $product(" + coeff.abs + ", " + atomicTerm(t, ctxt) + "))"))
        }
        case IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s) => {
          print("$difference(")
          TryAgain(s, addClosingString(ctxt, ", " + atomicTerm(t, ctxt) + ")"))
        }
        case IPlus(ITimes(coeff, AtomicTerm(t)), s) if (coeff.signum < 0) => {
          print("$difference(")
          TryAgain(
            s,
            addClosingString(
              ctxt,
              ", $product(" + coeff.abs + ", " + atomicTerm(t, ctxt) + "))"))
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
          print("$sum(")
          prefixNotation(ctxt, 2)
        }

        case ITimes(coeff, _) => {
          print("$product(" + coeff + ", ")
          prefixNotation(ctxt, 1)
        }
      
        case IFunApp(fun, _) => {
          fun match {
            case GroebnerMultiplication.mul | BitShiftMultiplication.mul =>
              print("$product")
            case f =>
              print(f.name)
          }
          print("(")
          if (fun.arity == 0) {
            print(")")
            KeepArg
          } else {
            prefixNotation(ctxt, fun.arity)
          }
        }
        
        case _ : ITermITE => {
          print("$ite_t(")
          prefixNotation(ctxt, 3)
        }

        case _ : IFormulaITE => {
          print("$ite_f(")
          prefixNotation(ctxt, 3)
        }

        // Formulae
        case IAtom(pred, _) => {
          print(pred.name)
          if (pred.arity > 0) {
            print("(")
            prefixNotation(ctxt, pred.arity)
          } else {
            noParentOp(ctxt)
          }
        }
        
        case IBinFormula(junctor, left, right) => {
          val op = junctor match {
            case IBinJunctor.And => " & "
            case IBinJunctor.Or => " | "
            case IBinJunctor.Eqv => " <=> "
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
          print("$" + value)
          noParentOp(ctxt)
        }

/*      
        case IIntFormula(IIntRelation.EqZero,
                         ITimes(IdealInt.MINUS_ONE, t)) => {
          print("0 = ")
          TryAgain(t, ctxt)
        }
*/

        case IEquation(_, _) => {
          allButLast(ctxt, " = ", "", 2)
        }

        case IIntFormula(IIntRelation.GeqZero,
                         ITimes(IdealInt.MINUS_ONE, t)) => {
          print("$lesseq(")
          TryAgain(t, ctxt setParentOp (", 0)"))
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          TryAgain(s, ctxt setParentOp (" = " + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.GeqZero,
                         IPlus(s, ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)))) => {
          print("$lesseq(" + atomicTerm(t, ctxt) + ", ")
          TryAgain(s, addClosingParen(ctxt))
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(s, ITimes(coeff, AtomicTerm(t)))) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" = $product(" + coeff.abs + ", " +
                                        atomicTerm(t, ctxt) + ")" + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          TryAgain(s, ctxt setParentOp (" = " + atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.GeqZero,
                         IPlus(ITimes(IdealInt.MINUS_ONE, AtomicTerm(t)), s)) => {
          print("$lesseq(" + atomicTerm(t, ctxt) + ", ")
          TryAgain(s, addClosingParen(ctxt))
        }
        case IIntFormula(IIntRelation.EqZero,
                         IPlus(ITimes(coeff, AtomicTerm(t)), s)) if (coeff.signum < 0) => {
          TryAgain(s, ctxt setParentOp (" = " + coeff.abs + "*" +
                                        atomicTerm(t, ctxt) + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.EqZero, IPlus(IIntLit(value), s)) => {
          TryAgain(s, ctxt setParentOp (" = " + (-value) + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.GeqZero, IPlus(IIntLit(value), s)) => {
          print("$lesseq(" + (-value) + ", ")
          TryAgain(s, addClosingParen(ctxt))
        }
        case IIntFormula(IIntRelation.EqZero, IPlus(s, IIntLit(value))) => {
          TryAgain(s, ctxt setParentOp (" = " + (-value) + ctxt.parentOp))
        }
        case IIntFormula(IIntRelation.GeqZero, IPlus(s, IIntLit(value))) => {
          print("$lesseq(" + (-value) + ", ")
          TryAgain(s, addClosingParen(ctxt))
        }
      
        case IIntFormula(IIntRelation.EqZero, _) => {
          UniSubArgs(ctxt setParentOp (" = 0"))
        }
      
        case IIntFormula(IIntRelation.GeqZero, _) => {
          print("$lesseq(0, ")
          prefixNotation(ctxt, 1)
        }
      
        case INot(subF) => {
          print(" ~ ")
          noParentOp(
            subF match {
              case _ : IIntFormula =>
                ctxt setPrecLevel 10
              case _ =>
                ctxt
            })
        }
        case ISortedQuantified(quan, sort, _) => {
          val varName = "v" + ctxt.vars.size
          print(quan match {
            case Quantifier.ALL => " !"
            case Quantifier.EX => " ?"
          })
          print(" [" + varName + ": " + sort + "] : ")
          noParentOp(ctxt pushVar varName)
        }
        case INamedPart(_, f) => {
          TryAgain(f, ctxt)
        }
        case ITrigger(_, f) => {
          TryAgain(f, ctxt)
        }
      }
    }
    
    def postVisit(t : IExpression,
                  ctxt : PrintContext, subres : Seq[Unit]) : Unit =
      print(ctxt.parentOp)
  
  }
}
