/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023-2025 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ExtArray, ADT, TheoryRegistry, Incompleteness}
import ap.types.{Sort, MonoSortedIFunction, MonoSortedPredicate, ProxySort}
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap,
                                 Set => MSet, ArrayBuffer}

object ArraySeqTheory {

  import IExpression.Sort
  
  private val AC = Debug.AC_SEQUENCE

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

class ArraySeqTheory(val ElementSort : Sort) extends SeqTheory
                                             with SMTLinearisableTheory {

  import ArraySeqTheory.AC

  val name = "Seq[" + ElementSort + "]"

  val arrayTheory = new ExtArray(List(Sort.Integer), ElementSort)

  private val arraySort =
    arrayTheory.sort
  private val emptyArray =
    IFunApp(arrayTheory.const, List(ElementSort.individuals.head))

  val (pairSort, seqPair, Seq(seqContents, seqSize)) =
    ADT.createRecordType(name, List(("seqContents", arrayTheory.sort),
                                    ("seqSize", Sort.Nat)))
  val pairTheory = pairSort.asInstanceOf[ADT.ADTProxySort].adtTheory

  object SeqSort extends ProxySort(pairSort) {
    import IExpression._

    override def individuals : LazyList[ITerm] = elementLists

    private lazy val elementLists : LazyList[ITerm] =
      seq_empty() #::
      (for (tail <- elementLists; t <- ElementSort.individuals)
       yield seq_cons(t, tail))

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      pairSort.augmentModelTermSet(model, terms, allTerms, definedTerms)

      val toRemove = new ArrayBuffer[(IdealInt, Sort)]

      for ((oldkey@(id, `pairSort`),
            IFunApp(`seqPair`,
                    Seq(contents, IIntLit(IdealInt(sizeInt))))) <- terms) {
        val contentsAr = new Array[ITerm] (sizeInt)

        var t = contents
        var cont = true
        while (cont) t match {
          case IFunApp(ExtArray.Store(_), Seq(t2, IIntLit(IdealInt(p)), v)) => {
            t = t2
            if (0 <= p && p < contentsAr.size)
              contentsAr(p) = v
          }
          case IFunApp(ExtArray.Const(_), Seq(v)) => {
            for (n <- 0 until contentsAr.size)
              if (contentsAr(n) == null)
                contentsAr(n) = v
            cont = false
          }
        }

        val constrTerm =
          contentsAr.foldRight(seq_empty())(seq_cons(_, _))

        terms.put((id, this), constrTerm)
        toRemove += oldkey
      }

      terms --= toRemove
    }

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get (d, this)
  }

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

  private val emptySeq = {
    import IExpression._
    seqPair(emptyArray, 0)
  }

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
        emptySeq
      case IFunApp(`seq_len`, _) =>
        seqSize(subres.head.asInstanceOf[ITerm])
      case IFunApp(`seq_unit`, _) =>
        seqPair(store(emptyArray, 0, subres.head.asInstanceOf[ITerm]), 1)
      case IFunApp(`seq_cons`, _) => {
        val head = subres.head.asInstanceOf[ITerm]
        val tail = subres.last.asInstanceOf[ITerm]
        withEps(tail, SeqSort, (cont, size) =>
          seqPair(arrayCopy(cont, store(emptyArray, 0, head), 0, size, 1),
                  size + 1)
        )
      }
      case IFunApp(`seq_++`, _) => {
        val left  = shiftVars(subres.head.asInstanceOf[ITerm], 0, 5)
        val right = shiftVars(subres.last.asInstanceOf[ITerm], 0, 5)
        SeqSort.eps(arraySort.ex(ex(arraySort.ex(ex(
          (seqPair(v(1, arraySort), v(0)) === left) &
          (seqPair(v(3, arraySort), v(2)) === right) &
          v(4, SeqSort) ===
            seqPair(arrayCopy(v(3, arraySort), v(1, arraySort), 0, v(2), v(0)),
                    v(0) + v(2)))))))
      }
      case IFunApp(`seq_extract`, _) => {
        val seq   = subres(0).asInstanceOf[ITerm]
        val start = subres(1).asInstanceOf[ITerm]
        val len   = subres(2).asInstanceOf[ITerm]
        withEps(seq, SeqSort, (cont, size) =>
          ite((0 <= start) & (0 <= len) & (start < size),
              seqPair(arrayCopy(cont, emptyArray,
                                start, min(List(start + len, size)), 0),
                      min(List(len, size - start))),
              emptySeq)
        )
      }
      case IFunApp(`seq_at`, _) => {
        val seq = subres(0).asInstanceOf[ITerm]
        val idx = subres(1).asInstanceOf[ITerm]
        withEps(seq, SeqSort, (cont, size) =>
          ite((0 <= idx) & (idx < size),
              seqPair(store(emptyArray, 0, select(cont, idx)), 1),
              emptySeq)
        )
      }
      case IFunApp(`seq_nth`, _) => {
        val seq = subres(0).asInstanceOf[ITerm]
        val idx = subres(1).asInstanceOf[ITerm]
        withEps(seq, ElementSort, (cont, size) =>
          ite((0 <= idx) & (idx < size),
              select(cont, idx),
              seq_nth(seqPair(cont, size), idx))
        )
      }

      case IFunApp(`seq_update`, _) => {
        val seq   = subres(0).asInstanceOf[ITerm]
        val idx   = subres(1).asInstanceOf[ITerm]
        val value = subres(2).asInstanceOf[ITerm]
        withEps(seq, SeqSort, (cont, size) =>
          ite((seqSize(value) === 1) & (0 <= idx) & (idx < size),
              seqPair(store(cont, idx, select(seqContents(value), 0)),
                      size),
              seqPair(cont, size)) // TODO
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

    private val contC = arraySort newConstant "contC"
    private val sizeC = IExpression.Sort.Integer newConstant "sizeC"

    private def withEps(seq     : ITerm,
                        resSort : Sort,
                        body    : (ITerm, ITerm) => ITerm) : ITerm = {
      val sseq  = shiftVars(seq, 0, 3)
      val sbody = ConstantSubstVisitor(shiftVars(body(contC, sizeC), 0, 3),
                                       Map(contC -> v(1, arraySort),
                                           sizeC -> v(0)))
      resSort.eps(arraySort.ex(ex((seqPair(v(1, arraySort), v(0)) === sseq) &
                                  (v(2, resSort) === sbody))))
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

  private def postSimplify(t : IExpression) : IExpression = {
    import IExpression._
    import arrayTheory.{select, store, const}

    t match {
      case IFunApp(`seqSize`, args) =>
        IFunApp(seq_len, args)
      case IFunApp(`select`, Seq(IFunApp(`seqContents`, Seq(s)), idx)) =>
        // TODO: correctly check bounds?
        IFunApp(seq_nth, Seq(s, idx))
      case IFunApp(`seqPair`, Seq(_, Const(IdealInt.ZERO))) =>
        IFunApp(seq_empty, Seq())
      case IFunApp(`seqPair`,
                   Seq(IFunApp(`store`, Seq(_, Const(IdealInt.ZERO), value)),
                       Const(IdealInt.ONE))) =>
        IFunApp(seq_unit, Seq(value))
      case t =>
        t
    }
  }

  override def postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ List(postSimplify _)

  //////////////////////////////////////////////////////////////////////////////

  override def fun2SMTString(f : IFunction) : Option[String] =
    f match {
      case `seq_len` | `seqSize` =>
        Some("seq.len")
      case `seq_empty` =>
        Some(f"(as seq.empty ${SMTLineariser.sort2SMTString(SeqSort)})")
      case f =>
        Some(f.name.replace("seq_", "seq."))
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
  SeqTheory register this

}
