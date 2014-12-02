/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import ap._
import ap.basetypes.IdealInt
import ap.theories._
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the SMT-LIB 2 format
 */
object SMTLineariser {

  private val SaneId     = """[_a-zA-Z][_a-zA-Z0-9]*""".r
  
  def quoteIdentifier(str : String) = str match {
    case SaneId() => str
    case _        => "|" + str.replace("|", "\\|") + "|"
  }

  //////////////////////////////////////////////////////////////////////////////

  def apply(formula : IFormula) = formula match {
    case IBoolLit(value) => print(value)
    case _ => {
      val lineariser = new SMTLineariser("", "", "", List(), List(), "", "", "")
      lineariser printFormula formula
    }
  }

  def apply(term : ITerm) = {
    val lineariser = new SMTLineariser("", "", "", List(), List(), "", "", "")
    lineariser printTerm term
  }

  def apply(formulas : Seq[IFormula], signature : Signature,
            benchmarkName : String) : Unit =
    apply(formulas, signature, "AUFLIA", "unknown", benchmarkName)

  def apply(formulas : Seq[IFormula], signature : Signature,
            logic : String, status : String,
            benchmarkName : String) : Unit = {
    val order = signature.order
    
    val (finalFormulas, constsToDeclare) : (Seq[IFormula], Set[ConstantTerm]) =
      if (Seqs.disjoint(order.orderedConstants, signature.existentialConstants)) {
        // if all constants are universal, we do not have to add explicit quantifiers
        (for (f <- formulas) yield ~f,
         signature.universalConstants ++ signature.nullaryFunctions)
      } else {
        val formula = IExpression.connect(formulas, IBinJunctor.Or)
        // add the nullary functions
        val withFunctions =
          IExpression.quanConsts(Quantifier.ALL, signature.nullaryFunctions, formula)
        // ... and the existentially quantified constants
        val withExConstants =
          IExpression.quanConsts(Quantifier.EX,
                                 signature.existentialConstants,
                                 withFunctions)
        // add the universally quantified constants
        val withUniConstants =
          IExpression.quanConsts(Quantifier.ALL,
                                 signature.universalConstants,
                                 withFunctions)
        
        (List(~withUniConstants), Set())
      }
    
    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
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
                    status : String,
                    constsToDeclare : Seq[ConstantTerm],
                    predsToDeclare : Seq[Predicate],
                    funPrefix : String, predPrefix : String, constPrefix : String) {

  import SMTLineariser.quoteIdentifier

  private def fun2Identifier(fun : IFunction) =
    (TheoryRegistry lookupSymbol fun) match {
      case Some(t : SimpleArray) => fun match {
        case t.select => "select"
        case t.store => "store"
      }
      case Some(BitShiftMultiplication) => fun match {
        case BitShiftMultiplication.mul => "*"
      }
      case _ =>
        quoteIdentifier(funPrefix + fun.name)
    }

  private def pred2Identifier(pred : Predicate) =
    quoteIdentifier(predPrefix + pred.name)
  private def const2Identifier(const : ConstantTerm) =
    quoteIdentifier(constPrefix + const.name)
  
  //////////////////////////////////////////////////////////////////////////////

  def open {
    println("(set-logic " + logic + ")")
    println("(set-info :source |")
    println("    Benchmark: " + benchmarkName)
    println("    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("|)")
  
    println("(set-info :status " + status + ")")

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
  
  def printTerm(term : ITerm) =
    AbsyPrinter.visit(term, PrintContext(List()))
  
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

      case _ : ITermITE | _ : IFormulaITE => {
        print("(ite ")
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
      case ITrigger(trigs, body) => {
        // we have to handle this case recursively, since the
        // order of the parameters has to be changed
        
        print("(! ")
        visit(body, ctxt)
        print(" :pattern (")
        for (t <- trigs)
          visit(t, ctxt)
        print(")) ")
        
        ShortCutResult()
      }
    }
    
    def postVisit(t : IExpression,
                  arg : PrintContext, subres : Seq[Unit]) : Unit = t match {
      case IPlus(_, _) | ITimes(_, _) | IAtom(_, Seq(_, _*)) | IFunApp(_, Seq(_, _*)) |
           IBinFormula(_, _, _) | IIntFormula(_, _) | INot(_) |
           IQuantified(_, _) | ITermITE(_, _, _) | IFormulaITE(_, _, _) =>
        print(") ")
      case IAtom(_, _) | IFunApp(_, _) =>
        // nothing
    }
  
  }
  
}
