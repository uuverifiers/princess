/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.theories.TheoryCollector
import ap.parameters.{ParserSettings, Param}
import ap.terfor.{ConstantTerm, OneTerm, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.Atom
import ap.util.{Debug, Logic, PlainRange}
import ap.basetypes.IdealInt

import scala.collection.mutable.{ArrayStack => Stack, ArrayBuffer}

object Parser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)
  
  def warn(msg : String) : Unit = Console.withOut(Console.err) {
    println("Warning: " + msg)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Class for removing all CR-characters in a stream (necessary because the
   * lexer seems to dislike CRs in comments). This also adds an LF in the end,
   * because the lexer does not allow inputs that end with a //-comment line
   * either
   */
  class CRRemover2(input : java.io.Reader) extends java.io.Reader {
  
    private val CR : Int = '\r'
    private val LF : Int = '\n'
    private var addedLF : Boolean = false
    
    def read(cbuf : Array[Char], off : Int, len : Int) : Int = {
      var read = 0
      while (read < len) {
        val next = input.read
        next match {
          case -1 =>
            if (addedLF) {
              return if (read == 0) -1 else read
            } else {
              cbuf(off + read) = LF.toChar
              read = read + 1
              addedLF = true
            }
          case CR => // nothing, read next character
          case _ => {
            cbuf(off + read) = next.toChar
            read = read + 1
          }
        }
      }
      read
    }
   
    def close : Unit = input.close
  
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Generate axioms for the (non-extensional) theory of arrays
   */
  def arrayAxioms(arity : Int, select : IFunction, store : IFunction) : IFormula = {
    import IExpression._
  
    val storeExp =
      IFunApp(store, for (i <- 0 until (arity + 2)) yield v(i))
    val selectExp =
      IFunApp(select, List(v(0)) ++ (for (i <- 0 until arity) yield v(i + arity + 2)))
    val selectStoreExp =
      IFunApp(select, List(storeExp) ++ (for (i <- 0 until arity) yield v(i + arity + 2)))
      
    quan(Array.fill(arity + 2){Quantifier.ALL},
      ITrigger(List(storeExp),
               IFunApp(select,
                       List(storeExp) ++ (for (i <- 1 to arity) yield v(i))) ===
               v(arity + 1))
    ) &
    quan(Array.fill(2*arity + 2){Quantifier.ALL},
      ITrigger(List(selectStoreExp),
               connect(for (i <- 1 to arity) yield (v(i) === v(i + arity + 1)),
                       IBinJunctor.And) |
               (selectStoreExp === selectExp))
    )
  }
}


abstract class Parser2InputAbsy[CT, VT, PT, FT]
                               (val env : Environment[CT, VT, PT, FT],
                                settings : ParserSettings) {
  
  import IExpression._
  
  def this(env : Environment[CT, VT, PT, FT]) =
    this(env, ParserSettings.DEFAULT)

  type GrammarExpression
  
  /**
   * Parse a problem from a character stream. The result is the formula
   * contained in the input, a list of interpolation specifications present
   * in the input, and the <code>Signature</code> declared in the input
   * (constants, and the <code>TermOrder</code> that was used for the formula).
   */
  def apply(input : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature)

  protected def genSignature(completeFor : IExpression) : Signature = {
    var prel = env.toSignature
    val coll = new TheoryCollector
    coll(completeFor)
    if (coll.theories.isEmpty) {
      prel
    } else {
      Signature(prel.universalConstants,
                prel.existentialConstants,
                prel.nullaryFunctions,
                prel.predicateMatchConfig ++ (
                  for (t <- coll.theories.iterator;
                       p <- t.predicateMatchConfig.iterator) yield p),
                (prel.order /: coll.theories) { case (o, t) => t extend o },
                coll.theories,
                prel.domainPredicates,
                prel.functionTypes)
    }
  }

  protected def genSignature(completeFor : IExpression,
                             funTypeConverter : FT => Signature.FunctionType)
                            : Signature = {
    var prel = env toSignature funTypeConverter
    val coll = new TheoryCollector
    coll(completeFor)
    if (coll.theories.isEmpty) {
      prel
    } else {
      Signature(prel.universalConstants,
                prel.existentialConstants,
                prel.nullaryFunctions,
                prel.predicateMatchConfig ++ (
                  for (t <- coll.theories.iterator;
                       p <- t.predicateMatchConfig.iterator) yield p),
                (prel.order /: coll.theories) { case (o, t) => t extend o },
                coll.theories,
                prel.domainPredicates,
                prel.functionTypes)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  protected abstract class ASTConnective {
    def unapplySeq(f : GrammarExpression) : Option[Seq[GrammarExpression]]
  }
  
  protected def collectSubExpressions(f : GrammarExpression,
                                      cont : GrammarExpression => Boolean,
                                      Connective : ASTConnective)
                                     : Seq[GrammarExpression] = {
    val todo = new Stack[GrammarExpression]
    val res = new ArrayBuffer[GrammarExpression]
    
    todo push f
    while (!todo.isEmpty) {
      val next = todo.pop
      
      if (cont(next)) next match {
        case Connective(subExpr @ _*) =>
          for (e <- subExpr) todo push e
      } else
        res += next
    }
    
    res
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val axioms = new ArrayBuffer[IFormula]

  protected def addAxiom(f : IFormula) = (axioms += f)
  protected def getAxioms : IFormula = connect(axioms, IBinJunctor.And)
  
  protected def defaultFunctionType(f : IFunction) : FT
  
  protected def mult(t1 : ITerm, t2 : ITerm) : ITerm =
    try { t1 * t2 }
    catch {
      case _ : IllegalArgumentException => {
//        throw new Parser2InputAbsy.TranslationException(
//                        "Do not know how to multiply " + t1 + " with " + t2)
//        genNonLinearMultAxioms
//        nonLinMult(t1, t2)
        val theory =
          Param.MUL_PROCEDURE(settings) match {
            case Param.MulProcedure.BitShift => ap.theories.BitShiftMultiplication
            case Param.MulProcedure.Native   => ap.theories.NIA.GroebnerMultiplication
          }
        if (!nonLinearMultDefined) {
          Parser2InputAbsy.warn(
            "using theory to encode multiplication: " + theory)
          nonLinearMultDefined = true
        }
        theory.mul(t1, t2)
      }
    }

  private var nonLinearMultDefined = false
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Declare functions <code>select, store</code> and generate axioms of the
   * (non-extensional) theory of arrays. The argument determines whether the
   * array functions should be declared as partial or as total functions
   */
  protected def genArrayAxioms(partial : Boolean,
                               arity : Int) : Unit =
    if (!(definedArrayArities contains arity)) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////
      Debug.assertPre(Parser2InputAbsy.AC, arity > 0)
      //-END-ASSERTION-/////////////////////////////////////////////////

      definedArrayArities += arity
       
      val (prefix, suffix) =
        if (arity == 1) {
          Parser2InputAbsy.warn("adding array axioms")
          ("", "")
        } else {
          Parser2InputAbsy.warn("adding array axioms for arity " + arity)
          ("_", "_" + arity)
        }
      
      val select = new IFunction(prefix + "select" + suffix, arity + 1, partial, false)
      val store = new IFunction(prefix + "store" + suffix, arity + 2, partial, false)
    
      env.addFunction(select, defaultFunctionType(select))
      env.addFunction(store, defaultFunctionType(store))

      addAxiom(Parser2InputAbsy.arrayAxioms(arity, select, store))
  }

  private var definedArrayArities = Set[Int]()

}
