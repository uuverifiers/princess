/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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
   * Transition of a transducer. The <code>constraint</code> is a formula over
   * variables <code>_0, _1, ...</code> representing the head symbols of the
   * transducer tracks. The <code>epsilons</code> tell which of the tracks
   * do not proceed to the next character.
   */
  case class TransducerTransition(fromState : Int,
                                  toState : Int,
                                  epsilons : Seq[Boolean],
                                  constraint : IFormula,
                                  blockedTransitions : Seq[BlockedTransition] =
                                    List())

  /**
   * For priority transducers, add transitions which must not lead to
   * accepting runs. Each instance of this class corresponds to a guard
   * <code> ! exists w1, ..., wk : String. state_n(...) </code>,
   * where the quantifiers correspond to the <code>quantifiedTracks</code>.
   */
  case class BlockedTransition(toState : Int, quantifiedTracks : Seq[Boolean])

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
