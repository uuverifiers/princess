/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap._
import ap.theories.{TheoryCollector, MulTheory}
import ap.parameters.{ParserSettings, Param}
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


abstract class Parser2InputAbsy[CT, VT, PT, FT, StackState]
                               (initialEnv : Environment[CT, VT, PT, FT],
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
    val coll = new TheoryCollector
    coll(completeFor)
    for (t <- coll.theories find (_.isInstanceOf[MulTheory]))
      Parser2InputAbsy.warn("using theory to encode multiplication: " + t)
    env.toSignature addTheories coll.theories
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add a new frame to the settings stack; this in particular affects the
   * <code>Environment</code>.
   */
  protected def pushState(state : StackState) : Unit = {
    storedStates push ((currentEnv, environmentCopied, axioms, state))
    environmentCopied = false
  }

  /**
   * Pop a frame from the settings stack.
   */
  protected def popState : StackState = {
    val (oldEnv, oldCopied, oldAxioms, oldState) = storedStates.pop
    currentEnv = oldEnv
    environmentCopied = oldCopied
    axioms = oldAxioms
    oldState
  }

  /**
   * Make sure that the current settings frame contains a local copy of
   * the <code>Environment</code>.
   * To be called before changing anything in the <code>Environment</code>.
   */
  protected def ensureEnvironmentCopy : Unit =
    if (!environmentCopied) {
      currentEnv = currentEnv.clone
      environmentCopied = true
    }

  /**
   * Erase all stored information.
   */
  protected def reset : Unit = {
    storedStates.clear
    currentEnv = initialEnv
    currentEnv.clear
    environmentCopied = true
    axioms = List()
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

  private val storedStates =
    new Stack[(Environment[CT, VT, PT, FT], Boolean, List[IFormula],
               StackState)]

  private var currentEnv : Environment[CT, VT, PT, FT] = initialEnv
  private var environmentCopied : Boolean = true

  def env : Environment[CT, VT, PT, FT] = currentEnv

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

  private var axioms : List[IFormula] = List()

  protected def addAxiom(f : IFormula) : Unit = (axioms = f :: axioms)
  protected def getAxioms : IFormula = connect(axioms, IBinJunctor.And)
  
  protected lazy val mulTheory : MulTheory =
    Param.MUL_PROCEDURE(settings) match {
      case Param.MulProcedure.BitShift => ap.theories.BitShiftMultiplication
      case Param.MulProcedure.Native   => ap.theories.nia.GroebnerMultiplication
    }
  
  protected def mult(t1 : ITerm, t2 : ITerm) : ITerm = mulTheory.mult(t1, t2)

}
