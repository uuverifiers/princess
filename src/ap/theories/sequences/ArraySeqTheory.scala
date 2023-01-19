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

import ap.Signature
import ap.algebra.Monoid
import ap.parser.{IFunction, ITerm, IFunApp, IExpression}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ExtArray, ADT, TheoryRegistry}
import ap.types.{Sort, MonoSortedIFunction, MonoSortedPredicate}
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.{HashMap => MHashMap}

object ArraySeqTheory {

  import IExpression.Sort
  
  private val instances = new MHashMap[Sort, ArraySeqTheory]

  /**
   * Get a unique instance of the array sequence theory with the given
   * element sort.
   */
  def apply(elementSort : Sort) : ArraySeqTheory = synchronized {
    instances.getOrElseUpdate(elementSort,
                              new ArraySeqTheory(elementSort))
  }

}

class ArraySeqTheory(val ElementSort : Sort) extends SeqTheory {

  val name = "Seq[" + ElementSort + "]"

  val arrayTheory = new ExtArray(List(Sort.Integer), ElementSort)

  val (seqSort, seqPair, Seq(seqContents, seqSize)) =
    ADT.createRecordType(name, List(("seqContents", arrayTheory.sort),
                                    ("seqSize", Sort.Nat)))
  val pairTheory = seqSort.asInstanceOf[ADT.ADTProxySort].adtTheory

  val SeqSort = seqSort

  override val dependencies = List(pairTheory, arrayTheory)

  //////////////////////////////////////////////////////////////////////////////

  private val ESo = ElementSort
  private val SSo = SeqSort
  import Sort.{Nat, Integer}

  val seq_empty =
    new MonoSortedIFunction("seq_empty", List(), SSo, true, false)
  val seq_cons =
    new MonoSortedIFunction("seq_cons", List(ESo, SSo), SSo, true, false)
  val seq_unit =
    new MonoSortedIFunction("seq_unit", List(ESo), SSo, true, false)

  val seq_++ =
    new MonoSortedIFunction("seq_++", List(SSo, SSo), SSo, true, false)
  val seq_len =
    new MonoSortedIFunction("seq_len", List(SSo), Nat, true, false)
  val seq_extract =
    new MonoSortedIFunction("seq_extract", List(SSo, Nat, Nat), SSo, true, false)
  val seq_indexof =
    new MonoSortedIFunction("seq_indexof",
                            List(SSo, ESo, Integer), Integer, true, false)
  val seq_at =
    new MonoSortedIFunction("seq_at", List(SSo, Nat), SSo, true, false)
  val seq_nth =
    new MonoSortedIFunction("seq_at", List(SSo, Nat), ESo, true, false)

  val seq_contains =
    new MonoSortedPredicate("seq_contains", List(SSo, SSo))
  val seq_prefixof =
    new MonoSortedPredicate("seq_prefixof", List(SSo, SSo))
  val seq_suffixof =
    new MonoSortedPredicate("seq_suffixof", List(SSo, SSo))
  val seq_replace =
    new MonoSortedIFunction("seq_replace",
                            List(SSo, SSo, SSo), SSo, true, false)

  //////////////////////////////////////////////////////////////////////////////

  val functions =
    List(seq_empty, seq_cons, seq_unit, seq_++, seq_len, seq_extract, seq_indexof,
         seq_at, seq_nth, seq_replace)
  val predefPredicates =
    List(seq_contains, seq_prefixof, seq_suffixof)

  val (funPredicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions)
  val predicates = predefPredicates ++ funPredicates

  val functionPredicateMapping = functions zip funPredicates
  val functionalPredicates = funPredicates.toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  def plugin = None

  TheoryRegistry register this

}
