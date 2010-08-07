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
          val scDefLc = LinearCombination.sum(Array((IdealInt.ONE, definition),
                                                    (IdealInt.MINUS_ONE, scLc)),
                                              curOrder)
          val newEq = EquationConj(scDefLc, curOrder)
          curEqs = EquationConj.conj(Array(newEq, curEqs), logger, curOrder)
        }
        case None => cont = false
      }
    }

    (curEqs, curOrder)
  }
}
