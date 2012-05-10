/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.basetypes.IdealInt
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the SMT-LIB 2 format
 */
object SMTLineariser {

  def apply(formula : IFormula) = {
    val lineariser = new SMTLineariser("", "", List(), List(), "", "", "")
    lineariser printFormula formula
  }

  def apply(formulas : Seq[IFormula], signature : Signature,
            benchmarkName : String) = {
    val order = signature.order
    
    val (finalFormulas, constsToDeclare) : (Seq[IFormula], Set[ConstantTerm]) =
      if (Seqs.disjoint(order.orderedConstants, signature.existentialConstants)) {
        // if all constants are universal, we do not have to add explicit quantifiers
        (for (f <- formulas) yield !f,
         signature.universalConstants ++ signature.nullaryFunctions)
      } else {
        val formula = IExpression.connect(formulas, IBinJunctor.Or)
        // add the nullary functions
        val withFunctions =
          IExpression.quan(Quantifier.ALL, signature.nullaryFunctions, formula)
        // ... and the existentially quantified constants
        val withExConstants =
          IExpression.quan(Quantifier.EX,
                           signature.existentialConstants,
                           withFunctions)
        // add the universally quantified constants
        val withUniConstants =
          IExpression.quan(Quantifier.ALL,
                           signature.universalConstants,
                           withFunctions)
        
        (List(!withUniConstants), Set())
      }
    
    val lineariser = new SMTLineariser(benchmarkName,
                                       "AUFLIA",
    		                           constsToDeclare.toList,
    		                           order.orderedPredicates.toList,
    		                           "fun", "pred", "const")
   
    lineariser.open
    for (f <- finalFormulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }
}

/**
 * Class for printing <code>IFormula</code>s in the SMT-Lib format
 */
class SMTLineariser(benchmarkName : String,
                    logic : String,
                    constsToDeclare : Seq[ConstantTerm],
                    predsToDeclare : Seq[Predicate],
                    funPrefix : String, predPrefix : String, constPrefix : String) {

  private val noGoodChar = """[^a-zA-Z0-9]""".r
  
  private def toIdentifier(str : String) = noGoodChar.replaceAllIn(str, "_")
  
  private def fun2Identifier(fun : IFunction) =
    funPrefix + toIdentifier(fun.name)
  private def pred2Identifier(pred : Predicate) =
    predPrefix + toIdentifier(pred.name)
  private def const2Identifier(const : ConstantTerm) =
    constPrefix + toIdentifier(const.name)
  
  //////////////////////////////////////////////////////////////////////////////

  def open {
    println("(set-logic " + logic + ")")
    println("(set-info :source |")
    println("    Benchmark: " + benchmarkName)
    println("    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("|)")
  
    println("(set-info :status unknown)")

    // declare the required predicates
    for (pred <- predsToDeclare) {
      print("(declare-fun " + pred2Identifier(pred) + " (")
      print((for (_ <- 1 to pred.arity) yield "Int") mkString " ")
      println(") Bool)")
    }
    
    // declare universal constants
    for (const <- constsToDeclare)
      println("(declare-fun " + const2Identifier(const) + " () Int)")
  }
  
  def printFormula(clauseName : String, formula : IFormula) {
    print("(" + clauseName + " ")
    printFormula(formula)
    println(")")
  }
  
  def printFormula(formula : IFormula) =
    AbsyPrinter.visit(formula, PrintContext(List()))
  
  def close {
    println("(check-sat)")
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def toSMTExpr(value : IdealInt) : String =
    if (value.signum < 0)
      "(- " + value.abs.toString + ")"
    else
      value.toString
  
  //////////////////////////////////////////////////////////////////////////////

  private case class PrintContext(vars : List[String]) {
    def pushVar(name : String) = PrintContext(name :: vars)
  }
  
  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    
    override def preVisit(t : IExpression,
                          ctxt : PrintContext) : PreVisitResult = t match {
      // Terms
      case IConstant(c) => {
        print(const2Identifier(c) + " ")
        ShortCutResult()
      }
      case IIntLit(value) => {
        print(toSMTExpr(value) + " ")
        ShortCutResult()
      }
      case IPlus(_, _) => {
        print("(+ ")
        KeepArg
      }
      case ITimes(coeff, _) => {
        print("(* " + toSMTExpr(coeff) + " ")
        KeepArg
      }
      case IVariable(index) => {
        print(ctxt.vars(index) + " ")
        ShortCutResult()
      }
      case IFunApp(fun, args) => {
        print((if (args.isEmpty) "" else "(") + fun2Identifier(fun) + " ")
        KeepArg
      }

      // Formulae
      case IAtom(pred, args) => {
        print((if (args.isEmpty) "" else "(") + pred2Identifier(pred) + " ")
        KeepArg
      }
      case IBinFormula(junctor, _, _) => {
        print("(")
        print(junctor match {
          case IBinJunctor.And => "and"
          case IBinJunctor.Or => "or"
          case IBinJunctor.Eqv => "="
        })
        print(" ")
        KeepArg
      }
      case IBoolLit(value) => {
        print(value + " ")
        ShortCutResult()
      }
      case IIntFormula(rel, _) => {
        print("(")
        print(rel match {
          case IIntRelation.EqZero => "="
          case IIntRelation.GeqZero => "<="
        })
        print(" 0 ")
        KeepArg
      }
      case INot(_) => {
        print("(not ")
        KeepArg
      }
      case IQuantified(quan, _) => {
        val varName = "var" + ctxt.vars.size
        print("(")
        print(quan match {
          case Quantifier.ALL => "forall"
          case Quantifier.EX => "exists"
        })
        print(" ((" + varName + " Int)) ")
        UniSubArgs(ctxt pushVar varName)
      }
    }
    
    def postVisit(t : IExpression,
                  arg : PrintContext, subres : Seq[Unit]) : Unit = t match {
      case IPlus(_, _) | ITimes(_, _) | IAtom(_, Seq(_, _*)) | IFunApp(_, Seq(_, _*)) |
           IBinFormula(_, _, _) | IIntFormula(_, _) | INot(_) |
           IQuantified(_, _) => print(") ")
      case IAtom(_, _) | IFunApp(_, _) => // nothing
    }
  
  }
  
}
