/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.theories.Theory
import ap.parser.smtlib.Absyn.{Sort => SSort, SymbolRef}
import ap.types.Sort

/**
 * Trait for theories with symbols that can be linearised through the
 * SMT-LIB front-end.
 */
trait SMTLinearisableTheory extends Theory {

  import SMTTypes.SMTType
  import IExpression.Predicate

  /**
   * Translate a sort belonging to this theory to an SMT type.
   */
  def sort2SMTType(s : Sort) : Option[SMTType] = None

  /**
   * Print an SMT-LIB declaration of this theory; do not output
   * anything if the theory does not need to be declared.
   */
  def printSMTDeclaration : Unit = ()

  /**
   * A list of (other) theories that are implicitly declared as a
   * side-effect of declaring this theory. We assume that theories can
   * implicitly define some of their dependencies, but not vice versa.
   */
  def SMTDeclarationSideEffects : Seq[Theory] = List()

  /**
   * Translate a function belonging to this theory to an SMT-LIB
   * identifier.
   */
  def fun2SMTString(f : IFunction) : Option[String] = None

  /**
   * Translate a predicate belonging to this theory to an SMT-LIB
   * identifier.
   */
  def pred2SMTString(p : Predicate) : Option[String] = None

}

/**
 * Trait for theories that can be parsed through the SMT-LIB
 * front-end. For analysing ASTs, the extractors in
 * <code>SMTParsingUtils</code> can be used. The trait does not extend
 * <code>Theory</code>, so that dependencies between theories, the
 * parsing library, and the AST classes can be avoided.
 */
trait SMTParseableTheory {

  import SMTTypes.SMTType

  /**
   * Translate a sort AST.
   */
  def translateSMTSortAST(s : SSort) : Option[SMTType] = None

  /**
   * Translate the application of a function or predicate. The
   * arguments can be translated recursively, given their polarity as
   * argument.
   */
  def translateSMTOperatorAST(
          sym       : SymbolRef,
          arguments : Seq[(Int) => (IExpression, SMTType)],
          polarity  : Int)
                    : Option[(IExpression, SMTType)] = None

}
