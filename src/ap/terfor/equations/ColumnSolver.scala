/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.equations;

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.util.Seqs

/**
 * Abstract class for solving a conjunction of equations through column
 * operations.
 */
abstract class ColumnSolver(equations : EquationConj,
                            logger : ComputationLogger, order : TermOrder) {

  private var curEqs = equations
  private var curOrder = order
  
  /**
   * Decide whether the given linear combination describes an equation that can
   * be solved/simplified through a column operation. This method has to be
   * implemented by subclasses and has to return <code>None</code> if the equation
   * cannot be simplified, otherwise a triplet consisting of the new "small symbol",
   * the term that the small symbol is supposed to represent, and the updated
   * <code>TermOrder</code>
   */
  protected def isSolvableEq(lc : LinearCombination, order : TermOrder)
                               : Option[(Term, LinearCombination, TermOrder)]

  lazy val result = {
    var cont : Boolean = true    
    while (cont && !curEqs.isFalse) {
      Seqs.some(for (lc <- curEqs.iterator) yield isSolvableEq(lc, curOrder)) match {
        case Some((smallConst, definition, newOrder)) => {
          curOrder = newOrder
          val scLc = LinearCombination(smallConst, curOrder)
          val scDefLc = definition.-(scLc)(curOrder)
          val newEq = EquationConj(scDefLc, curOrder)
          curEqs = EquationConj.conj(Array(newEq, curEqs), logger, curOrder)
        }
        case None => cont = false
      }
    }

    (curEqs, curOrder)
  }
}
