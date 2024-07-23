/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2019 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap._
import ap.theories.{TheoryCollector, MulTheory, Theory}
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


abstract class Parser2InputAbsy[CT, VT, PT, FT, ST, StackState]
                               (initialEnv : Environment[CT, VT, PT, FT, ST],
                                settings : ParserSettings) {
  
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

  // TODO: also push/pop/reset the theory collector
  // (this functionality is currently not used anywhere)
  private val theoryCollector = new TheoryCollector

  protected def addTheory(t : Theory) : Unit =
    theoryCollector addTheory t

  protected def genSignature(completeFor : IExpression) : Signature = {
    theoryCollector(completeFor)
    env.toSignature addTheories theoryCollector.theories
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
    val (oldEnv, oldCopied, oldAxioms, oldState) = storedStates.pop()
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

  private val storedStates =
    new Stack[(Environment[CT, VT, PT, FT, ST], Boolean, List[IFormula],
               StackState)]

  private var currentEnv : Environment[CT, VT, PT, FT, ST] = initialEnv
  private var environmentCopied : Boolean = true

  def env : Environment[CT, VT, PT, FT, ST] = currentEnv

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
      val next = todo.pop()
      
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
      case Param.MulProcedure.Native   => ap.theories.GroebnerMultiplication
    }
  
  protected def mult(t1 : ITerm, t2 : ITerm) : ITerm = mulTheory.mult(t1, t2)

}
