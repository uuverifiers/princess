/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.theories.strings

import ap.parser.IFormula
import ap.theories.TheoryBuilder

object StringTheoryBuilder {

  def apply(desc : String) : StringTheoryBuilder =
    TheoryBuilder(desc).asInstanceOf[StringTheoryBuilder]

  /**
   * n-track transducers represented as a set of transitions over the states
   * <code>0, 1, ..., n</code> with symbolic labels.
   */
  case class SymTransducer(transitions : Seq[TransducerTransition],
                           accepting : Set[Int])

  /**
   * Transition of a transducer. The constraint is a formula over
   * variables <code>_0, _1, ...</code> representing the head symbols of the
   * transducer tracks.
   */
  case class TransducerTransition(fromState : Int,
                                  toState : Int,
                                  epsilons : Seq[Boolean],
                                  constraint : IFormula)

}

/**
 * Interface to construct string theory objects with complex parameters.
 */
abstract class StringTheoryBuilder extends TheoryBuilder {

  type T = StringTheory

  def setAlphabetSize(w : Int) : Unit

  /**
   * Optionally, return a simplified string theory used to parse transducers
   * represented as recursive functions. Return <code>None</code> if the
   * string theory does not support transducers.
   */
  def getTransducerTheory : Option[StringTheory]

  /**
   * Add a transducer to the constructed string theory.
   */
  def addTransducer(name : String,
                    transducer : StringTheoryBuilder.SymTransducer) : Unit

}