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

package ap.parser;

import ap._
import ap.terfor.{ConstantTerm, OneTerm, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.{Predicate, Atom}
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
}


abstract class Parser2InputAbsy (protected val env : Environment) {
  
  import IExpression._
  
  type GrammarExpression
  
  /**
   * Parse a problem from a character stream. The result is the formula
   * contained in the input, a list of interpolation specifications present
   * in the input, and the <code>Signature</code> declared in the input
   * (constants, and the <code>TermOrder</code> that was used for the formula).
   */
  def apply(input : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature)

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
  
  protected def mult(t1 : ITerm, t2 : ITerm) : ITerm =
    try { t1 * t2 }
    catch {
      case _ : IllegalArgumentException => {
//        throw new Parser2InputAbsy.TranslationException(
//                        "Do not know how to multiply " + t1 + " with " + t2)
        genNonLinearMultAxioms
        nonLinMult(t1, t2)
      }
    }

  private var nonLinMult : IFunction = _
    
  protected def genNonLinearMultAxioms : Unit = if (!nonLinearMultDefined) {
    Parser2InputAbsy.warn("introducing partial function \"nonLinMult\" to encode multiplication")
    nonLinearMultDefined = true
    
    nonLinMult = new IFunction("nonLinMult", 2, true, false)
    env addFunction nonLinMult
    
    /*
        \forall int x; {nonLinMult(x, 0)} nonLinMult(x, 0) = 0
      &
        \forall int x; {nonLinMult(x, -1)} nonLinMult(x, -1) = -x
      &
        \forall int x, y, res; {nonLinMult(x, y)}
          ((y >= 1 | y <= -2) -> nonLinMult(x, y) = res ->
              \exists int l, n, subres; (
                 nonLinMult(2*x, l) = subres &
                 y = 2*l + n & (
                   n = 0 & res = subres
                   |
                   n = 1 & res = subres + x
       )))
    */
    
    addAxiom(
      all(ITrigger(List(nonLinMult(v(0), 0)),
                   nonLinMult(v(0), 0) === 0)))
    addAxiom(
      all(ITrigger(List(nonLinMult(v(0), -1)),
                   nonLinMult(v(0), -1) === -v(0))))
    addAxiom(
      all(all(all(
        ITrigger(List(nonLinMult(v(0), v(1))),
          (((v(1) >= 1 | v(1) <= -2) & nonLinMult(v(0), v(1)) === v(2)) ==>
              ex(ex(ex(
                 (nonLinMult(2*v(3), v(0)) === v(2)) &
                 (v(4) === 2*v(0) + v(1)) & (
                   (v(1) === 0 & v(5) === v(2))
                   |
                   (v(1) === 1 & v(5) === v(2) + v(3))
                  ))))))))))
  }
    
  private var nonLinearMultDefined = false
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Declare functions <code>select, store</code> and generate axioms of the
   * (non-extensional) theory of arrays. The argument determines whether the
   * array functions should be declared as partial or as total functions
   */
  protected def genArrayAxioms(partial : Boolean) : Unit = if (!arraysDefined) {
    Parser2InputAbsy.warn("adding array axioms")
    arraysDefined = true
        
    val select = new IFunction("select", 2, partial, false)
    val store = new IFunction("store", 3, partial, false)
    
    env addFunction select
    env addFunction store

    addAxiom(
      all(all(all(
          ITrigger(List(store(v(0), v(1), v(2))),
                   select(store(v(0), v(1), v(2)), v(1)) === v(2))
      ))) &
      all(all(all(all(
          ITrigger(List(select(store(v(0), v(1), v(2)), v(3))),
                   (v(1) === v(3)) |
                   (select(store(v(0), v(1), v(2)), v(3)) === select(v(0), v(3))))
      )))))
  }
  
  private var arraysDefined = false

}
