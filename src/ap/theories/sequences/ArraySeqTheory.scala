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
import ap.parser._
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ExtArray, ADT, TheoryRegistry, Incompleteness}
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

  private val arraySort =
    arrayTheory.sort
  private val emptyArray =
    IFunApp(arrayTheory.const, List(ElementSort.individuals.head))

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
    new MonoSortedIFunction("seq_extract", List(SSo, Nat, Nat), SSo, true,false)
  val seq_indexof =
    new MonoSortedIFunction("seq_indexof",
                            List(SSo, ESo, Integer), Integer, true, false)
  val seq_at =
    new MonoSortedIFunction("seq_at", List(SSo, Nat), SSo, true, false)
  val seq_nth =
    new MonoSortedIFunction("seq_nth", List(SSo, Nat), ESo, true, false)

  val seq_update =
    new MonoSortedIFunction("seq_update", List(SSo, Nat, SSo), SSo, true, false)

  val seq_contains =
    new MonoSortedPredicate("seq_contains", List(SSo, SSo))
  val seq_prefixof =
    new MonoSortedPredicate("seq_prefixof", List(SSo, SSo))
  val seq_suffixof =
    new MonoSortedPredicate("seq_suffixof", List(SSo, SSo))
  val seq_replace =
    new MonoSortedIFunction("seq_replace",
                            List(SSo, SSo, SSo), SSo, true, false)

  // arrayCopy(source, target, start, end, targetStart)
  // copies the range [start, end) from the array "source" to "target",
  // starting at "targetStart". 
  val arrayCopy =
    new MonoSortedIFunction("arrayCopy",
                            List(arraySort, arraySort,
                                 Integer, Integer, Integer),
                            arraySort,
                            true, true)

  //////////////////////////////////////////////////////////////////////////////

  val allAxioms = {
    import IExpression._
    import arrayTheory.{select, store}

    arraySort.all((source, target, result) =>
      Integer.all((start, end, targetStart) =>
        ITrigger(
          List(arrayCopy(source, target, start, end, targetStart)),
          (result === arrayCopy(source, target, start, end, targetStart)) ==>
          ite(start < end,
              result ===
                arrayCopy(source,
                          store(target, targetStart, select(source, start)),
                          start + 1, end, targetStart + 1),
              result === target)
        )
      )
    )
  }

  //////////////////////////////////////////////////////////////////////////////

  val functions =
    List(seq_empty, seq_cons, seq_unit, seq_++, seq_len, seq_extract,
         seq_indexof, seq_at, seq_nth, seq_update, seq_replace, arrayCopy)
  val predefPredicates =
    List(seq_contains, seq_prefixof, seq_suffixof)

  val (funPredicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms    = allAxioms,
                     otherTheories   = dependencies)
  val predicates = predefPredicates ++ funPredicates

  val functionPredicateMapping = functions zip funPredicates
  val functionalPredicates = funPredicates.toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  def plugin = None

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor called during pre-processing to eliminate symbols.
   */
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._
    import arrayTheory.{select, store, const}

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`seq_empty`, _) =>
        seqPair(emptyArray, 0)
      case IFunApp(`seq_len`, _) =>
        seqSize(subres.head.asInstanceOf[ITerm])
      case IFunApp(`seq_unit`, _) =>
        seqPair(store(emptyArray, 0, subres.head.asInstanceOf[ITerm]), 1)
      case IFunApp(`seq_cons`, _) => {
        val head = subres.head.asInstanceOf[ITerm]
        val tail = subres.last.asInstanceOf[ITerm]
        seqPair(arrayCopy(seqContents(tail), store(emptyArray, 0, head),
                          0, seqSize(tail), 1),
                seqSize(tail) + 1)
      }
      case IFunApp(`seq_++`, _) => {
        val left  = subres.head.asInstanceOf[ITerm]
        val right = subres.last.asInstanceOf[ITerm]
        seqPair(arrayCopy(seqContents(right), seqContents(left),
                          0, seqSize(right), seqSize(left)),
                seqSize(left) + seqSize(right))
      }
      case IFunApp(`seq_extract`, _) => {
        val seq   = subres(0).asInstanceOf[ITerm]
        val start = subres(1).asInstanceOf[ITerm]
        val len   = subres(2).asInstanceOf[ITerm]
        ite((0 <= start) & (start + len <= seqSize(seq)),
            seqPair(arrayCopy(seqContents(seq), emptyArray,
                              start, start + len, 0), len),
            seqPair(emptyArray, 0))
      }
      case IFunApp(`seq_at`, _) => {
        val seq = subres(0).asInstanceOf[ITerm]
        val idx = subres(1).asInstanceOf[ITerm]
        seqPair(store(emptyArray, 0, select(seqContents(seq), idx)), 1)
      }
      case IFunApp(`seq_nth`, _) => {
        val seq = subres(0).asInstanceOf[ITerm]
        val idx = subres(1).asInstanceOf[ITerm]
        select(seqContents(seq), idx)
      }
      case IFunApp(`seq_update`, _) => {
        val seq   = subres(0).asInstanceOf[ITerm]
        val idx   = subres(1).asInstanceOf[ITerm]
        val value = subres(2).asInstanceOf[ITerm]
        ite(seqSize(value) === 1,
            seqPair(store(seqContents(seq), idx,
                          select(seqContents(value), 0)),
                    seqSize(seq)),
            seqPair(emptyArray, 0) // TODO
        )
      }
      case IFunApp(`seq_indexof` | `seq_replace`, _) => {
        Incompleteness.set
        t update subres
      }
      case IAtom(`seq_contains` | `seq_prefixof` | `seq_suffixof`, _) => {
        Incompleteness.set
        t update subres
      }
      case t =>
        t update subres
    }
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) = {
//    println("before: " + f)
    val res = Preproc.visit(f, ()).asInstanceOf[IFormula]
//    println("after: " + res)
    (res, signature)
  }

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  TheoryRegistry register this

}
