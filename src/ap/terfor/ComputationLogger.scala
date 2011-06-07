/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor

import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.equations.EquationConj
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object ComputationLogger {
  private val AC = Debug.AC_COMPUTATION_LOGGER
  
  class NonLoggingLogger extends {
    val isLogging = false    
  } with ComputationLogger {
    def combineEquations(equations : Seq[(IdealInt, LinearCombination)],
                         result : LinearCombination,
                         resultAfterRounding : LinearCombination,
                         order : TermOrder) : Unit = {}
    def reduceNegEquation(equations : Seq[(IdealInt, LinearCombination)],
                          targetLit : LinearCombination,
                          order : TermOrder) : Unit = {}
    def reduceInequality(equations : Seq[(IdealInt, LinearCombination)],
                         targetLit : LinearCombination,
                         order : TermOrder) : Unit = {}
    def reducePredFormula(equations : Seq[Seq[(IdealInt, LinearCombination)]],
                          targetLit : Atom, negated : Boolean, result : Atom,
                          order : TermOrder) : Unit = {}
    def combineInequalities(leftCoeff : IdealInt, leftInEq : LinearCombination,
                            rightCoeff : IdealInt, rightInEq : LinearCombination,
                            result : LinearCombination,
                            resultAfterRounding : LinearCombination,
                            order : TermOrder) : Unit = {}
    def antiSymmetry(leftInEq : LinearCombination, rightInEq : LinearCombination,
                     order : TermOrder) : Unit = {}
    def directStrengthen(inequality : LinearCombination, equation : LinearCombination,
                         result : LinearCombination, order : TermOrder) : Unit = {}
    def groundInstantiateQuantifier(quantifiedFormula : Conjunction,
                                    instanceTerms : Seq[LinearCombination],
                                    result : Conjunction,
                                    order : TermOrder) : Unit = {}
    def unifyPredicates(leftAtom : Atom, rightAtom : Atom,
                        result : EquationConj, order : TermOrder) : Unit = {}
  }

  val NonLogger = new NonLoggingLogger

  abstract class LogScope[Input, Result](logging : Boolean) {
    private var logInput : Option[Input] = None

    def inProgress : Boolean = logInput.isDefined
    
    def log(input : Input, result : Result) : Unit
    
    def start[A](input : => Input)(body : => A) : A =
      if (logging) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, logInput.isEmpty)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        logInput = Some(input)
        try {
          body
        } finally {
          logInput = None
        }
      } else {
        body
      }

    def finish(result : Result) : Unit =
      if (logging && logInput.isDefined) {
        log(logInput.get, result)
        logInput = None
      }
  }
}

/**
 * Trait that can be used to track the computation taking place in systems of
 * equations, inequalities, etc. This is used to produce proofs.
 */
trait ComputationLogger {
  import ComputationLogger.LogScope
  
  val isLogging : Boolean
  
  /**
   * Inference corresponding to a series of applications of the reduce rule:
   * form the linear combination of a number of positive equations. The
   * given terms (apart from <code>result</code>) shall be primitive, with
   * a positive leading coefficient
   */
  def combineEquations(equations : Seq[(IdealInt, LinearCombination)],
                       result : LinearCombination,
                       resultAfterRounding : LinearCombination,
                       order : TermOrder) : Unit

  /**
   * Inference corresponding to a series of applications of the reduce rule to a
   * negated equation (reduction of positive equalities is
   * described using <code>CombineEquationsInference</code>).
   */
  def reduceNegEquation(equations : Seq[(IdealInt, LinearCombination)],
                        targetLit : LinearCombination, order : TermOrder) : Unit

  /**
   * Inference corresponding to a series of applications of the reduce rule to a
   * an inequality (reduction of positive equalities is
   * described using <code>CombineEquationsInference</code>).
   */
  def reduceInequality(equations : Seq[(IdealInt, LinearCombination)],
                       targetLit : LinearCombination, order : TermOrder) : Unit

  /**
   * Inference corresponding to a series of applications of the reduce rule to
   * the arguments of a predicate literal. This is essentially the same as the
   * <code>reduceArithFormula</code>, only that all of the arguments can be
   * reduced simultaneously
   */
  def reducePredFormula(equations : Seq[Seq[(IdealInt, LinearCombination)]],
                        targetLit : Atom, negated : Boolean, result : Atom,
                        order : TermOrder) : Unit

  /**
   * Fourier-Motzkin Inference. The given terms shall be primitive, which means
   * that the result will be implicitly rounded 
   */
  def combineInequalities(leftCoeff : IdealInt, leftInEq : LinearCombination,
                          rightCoeff : IdealInt, rightInEq : LinearCombination,
                          result : LinearCombination,
                          resultAfterRounding : LinearCombination,
                          order : TermOrder) : Unit

  /**
   * Turn two complementary inequalities into an equation
   */
  def antiSymmetry(leftInEq : LinearCombination, rightInEq : LinearCombination,
                   order : TermOrder) : Unit

  /**
   * Given the two formulae <code>t >= 0</code> and <code>t != 0</code> (or,
   * similarly, <code>t >= 0</code> and <code>-t != 0</code>), infer
   * the inequality <code>t-1 >= 0</code>.
   */
  def directStrengthen(inequality : LinearCombination, equation : LinearCombination,
                       result : LinearCombination, order : TermOrder) : Unit

  /**
   * Instantiate a universally quantified formula with ground terms
   */
  def groundInstantiateQuantifier(quantifiedFormula : Conjunction,
                                  instanceTerms : Seq[LinearCombination],
                                  result : Conjunction, order : TermOrder) : Unit

  /**
   * Unify two predicates, producing a
   * system of equations (in the succedent) that express the unification
   * conditions: the predicate arguments are matched pair-wise
   */
  def unifyPredicates(leftAtom : Atom, rightAtom : Atom,
                      result : EquationConj, order : TermOrder) : Unit
  
  //////////////////////////////////////////////////////////////////////////////
  // Some convenience methods that ease logging

  /**
   * Convenient interface for <code>combineEquations</code>
   */
  val ceScope =
    new LogScope[(Seq[(IdealInt, LinearCombination)], TermOrder),
                 (LinearCombination, LinearCombination)](isLogging) {
      def log(input : (Seq[(IdealInt, LinearCombination)], TermOrder),
              result : (LinearCombination, LinearCombination)) : Unit =
        combineEquations(input _1, result _1, result _2, input _2)
    }

  /**
   * Convenient interface for <code>combineInequalities</code>
   */
  val cieScope =
    new LogScope[(IdealInt, LinearCombination, IdealInt, LinearCombination, TermOrder),
                 (LinearCombination, LinearCombination)](isLogging) {
      def log(input : (IdealInt, LinearCombination, IdealInt, LinearCombination,
                       TermOrder),
              result : (LinearCombination, LinearCombination)) : Unit =
        combineInequalities(input _1, input _2, input _3, input _4,
                            result _1, result _2, input _5)
    }
}
