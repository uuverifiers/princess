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

package ap.theories.sequences

import ap.algebra.Monoid
import ap.parser.{IFunction, ITerm, IFunApp}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, TheoryRegistry}
import ap.types.Sort
import ap.terfor.conjunctions.Conjunction

object SeqTheory {

  /**
   * Extractor to recognise the string <code>str.empty</code> function.
   */
  object SeqEmpty {
    def unapply(f : IFunction) : Option[SeqTheory] =
      (TheoryRegistry lookupSymbol f) match {
        case Some(t : SeqTheory) if f == t.seq_empty => Some(t)
        case _ => None
      }
  }

  /**
   * Extractor to recognise the string <code>str.cons</code> function.
   */
  object SeqCons {
    def unapply(f : IFunction) : Option[SeqTheory] =
      (TheoryRegistry lookupSymbol f) match {
        case Some(t : SeqTheory) if f == t.seq_cons => Some(t)
        case _ => None
      }
  }

  object ConcreteSeq {
    def unapply(t : ITerm) : Option[List[ITerm]] = t match {
      case IFunApp(SeqCons(_), Seq(head, ConcreteSeq(tail))) =>
        Some(head :: tail)
      case IFunApp(SeqEmpty(_), _) =>
        Some(List())
      case _ =>
        None
    }
  }

}

trait SeqTheory extends Theory {

  /**
   * Sort representing sequences
   */
  val SeqSort     : Sort

  /**
   * Sort representing sequences
   */
  def sort = SeqSort

  /**
   * Sort representing sequence elements
   */
  val ElementSort : Sort

  // Representation functions

  val seq_empty      : IFunction    // -> SeqSort
  val seq_cons       : IFunction    // ElementSort x SeqSort -> SeqSort

  val seq_unit       : IFunction    // ElementSort -> SeqSort

  val seq_++         : IFunction    // SeqSort x SeqSort -> SeqSort
  val seq_len        : IFunction    // SeqSort -> Nat
  val seq_extract    : IFunction    // SeqSort x Nat x Nat -> SeqSort

  val seq_indexof    : IFunction    // SeqSort x ElementSort x Int -> Int

  val seq_at         : IFunction    // SeqSort x Nat -> SeqSort
  val seq_nth        : IFunction    // SeqSort x Nat -> ElementSort

  val seq_update     : IFunction    // SeqSort x Nat x SeqSort -> SeqSort

  val seq_contains   : Predicate    // SeqSort x SeqSort -> Boolean

  val seq_prefixof   : Predicate    // SeqSort x SeqSort -> Boolean
  val seq_suffixof   : Predicate    // SeqSort x SeqSort -> Boolean
  
  val seq_replace    : IFunction    // SeqSort x SeqSort x SeqSort
                                    //  -> SeqSort

  // seq.map
  // seq.mapi
  // seq.fold_left
  // seq.fold_lefti

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert a sequence to a term
   */
  implicit def seq2Term(seq : Seq[ITerm]) : ITerm =
    (seq :\ IFunApp(seq_empty, List())) {
      case (c, s) => IFunApp(seq_cons, List(c, s))
    }

}

/**
 * Every string theory gives rise to a monoid.
 */
case class SeqMonoid(seqTheory : SeqTheory) extends Monoid {

  val dom =
    seqTheory.SeqSort

  def op(s : ITerm, t : ITerm) : ITerm =
    IFunApp(seqTheory.seq_++, List(s, t))
  
  def identity : ITerm =
    IFunApp(seqTheory.seq_empty, List())

}
