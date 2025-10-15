/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.heaps

import ap.Signature
import ap.basetypes.IdealInt
import ap.theories.{Theory, TheoryRegistry, ADT, ExtArray}
import ap.types.{Sort, MonoSortedIFunction, MonoSortedPredicate, ProxySort}
import ap.parser._
import ap.terfor.{ConstantTerm, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.util.Debug

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashSet => MHashSet, Map => MMap, Set => MSet,
                                 ArrayBuffer, HashMap => MHashMap}

object ArrayHeap {

  private val AC = Debug.AC_HEAP

  /**
   * Natural numbers starting at 1.
   */
  val Nat1 = Sort.Interval(Some(IdealInt.ONE), None)

}

/**
 * A theory of heaps implemented using arrays.
 *
 * At the moment, extensionality and the batch operations are not fully
 * implemented yet.
 */
class ArrayHeap(heapSortName         : String,
                addressSortName      : String,
                addressRangeSortName : String,
                objectSort           : IHeap.ADTSort,
                userSortNames        : Seq[String],
                ctorSignatures       : Seq[(String, IHeap.CtorSignature)],
                defaultObjectCtor    : Seq[MonoSortedIFunction] => ITerm)
      extends IHeap {
  import IHeap._
  import ArrayHeap._
  import Sort.{Nat, Integer}

  val name = "ArrayHeap[" + heapSortName + "]"

  val userHeapCtorSignatures = ctorSignatures

  val userSortNum        = userSortNames.size
  val addressSortId      = userSortNum
  val addressRangeSortId = userSortNum + 1
  val nullAddrCtorId     = ctorSignatures.size
  val nthAddrCtorId      = ctorSignatures.size + 1
  val addressRangeCtorId = ctorSignatures.size + 2

  //////////////////////////////////////////////////////////////////////////////

  /**
   * ADT for all objects that can potentially be stored on the heap.
   */
  val onHeapADT = {
    def convSort(s : CtorArgSort) : ADT.CtorArgSort =
      s match {
        case ADTSort(num)  => ADT.ADTSort(num)
	    case OtherSort(s)  => ADT.OtherSort(s)
	    case AddrSort      => ADT.ADTSort(addressSortId)
	    case AddrRangeSort => ADT.ADTSort(addressRangeSortId)
      }

    val userCtors =
      for ((name, CtorSignature(arguments, result)) <- ctorSignatures) yield {
        val newArgs = arguments.map { case (n, s) => (n, convSort(s)) }
        (name, ADT.CtorSignature(newArgs, convSort(result).asInstanceOf[ADT.ADTSort]))
      }

    val ONat = ADT.OtherSort(Nat)
    val ONat1 = ADT.OtherSort(Nat1)

    val additionalCtors =
      List(("null" + addressSortName,
            ADT.CtorSignature(List(),
	                            ADT.ADTSort(addressSortId))),
	         ("nth" + addressSortName,
            ADT.CtorSignature(List((addressSortName + "_ord", ONat1)),
	                            ADT.ADTSort(addressSortId))),
           ("nth" + addressSortName + "Range",
            ADT.CtorSignature(List((addressSortName + "_start", ONat1),
	                                 (addressSortName + "_size", ONat)),
	                            ADT.ADTSort(addressRangeSortId))))

    val allCtors = userCtors ++ additionalCtors

    new ADT(userSortNames ++ List(addressSortName, addressRangeSortName),
    	      allCtors)
  }

  val AddressSort          = onHeapADT.sorts(addressSortId)
  val AddressRangeSort     = onHeapADT.sorts(addressRangeSortId)
  val ObjectSort           = onHeapADT.sorts(objectSort.num)
  val userHeapSorts        = onHeapADT.sorts.take(userSortNum)
  
  val nullAddr             = onHeapADT.constructors(nullAddrCtorId)
  val nthAddr              = onHeapADT.constructors(nthAddrCtorId)
  val nthAddrRange         = onHeapADT.constructors(addressRangeCtorId)
  val userHeapConstructors = onHeapADT.constructors.take(ctorSignatures.size)
  val userHeapSelectors    = onHeapADT.selectors.take(ctorSignatures.size)
  val userHeapUpdators     = onHeapADT.updators.take(ctorSignatures.size)

  val Seq(addrOrd)         = onHeapADT.selectors(nthAddrCtorId)
  val Seq(addressRangeStart, addressRangeSize)
                           = onHeapADT.selectors(addressRangeCtorId)

  val defaultObject        = defaultObjectCtor(userHeapConstructors)

  def hasUserHeapCtor(t : ITerm, id : Int) : IFormula = onHeapADT.hasCtor(t, id)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Arrays used to represent heap contents.
   */
  val arrayTheory =
    new ExtArray(List(Nat1), ObjectSort) {
      override def equalityPropagationEnabled = false
    }

  val ArraySort = arrayTheory.sort

  private val emptyArray = IFunApp(arrayTheory.const, List(defaultObject))

  /**
   * ADT for all things that cannot be on the heap.
   */
  val offHeapADT = {
    import ADT.{CtorSignature, OtherSort, ADTSort}
    def b(n : String) = heapSortName + "_" + n

    val ctors =
      List((b("ctor"),
	        CtorSignature(List((b("contents"), OtherSort(ArraySort)),
			                   (b("size"), OtherSort(Nat))),
		                  ADTSort(0))),
           (b("allocRes_ctor"),
	        CtorSignature(List(("new" + heapSortName, ADTSort(0)),
			                   ("new" + addressSortName,
                                              OtherSort(AddressSort))),
		                  ADTSort(1))),
	       (b("batchAllocRes_ctor"),
	        CtorSignature(List(("newBatch" + heapSortName, ADTSort(0)),
			                   ("new" + addressRangeSortName,
			                                  OtherSort(AddressRangeSort))),
		                  ADTSort(2))))

    new ADT(List(heapSortName,
                 "AllocRes" + heapSortName,
                 "BatchAllocRes" + heapSortName),
            ctors)
  }

  val rawHeapSort       = offHeapADT.sorts(0)
  val AllocResSort      = offHeapADT.sorts(1)
  val BatchAllocResSort = offHeapADT.sorts(2)

  val Seq(heapPair, allocResPair, batchAllocResPair) = offHeapADT.constructors

  val Seq(Seq(heapContents,      heapSize),
          Seq(allocResHeap,      allocResAddr),
	      Seq(batchAllocResHeap, batchAllocResAddr)) = offHeapADT.selectors

  private val _heapPair = offHeapADT.constructorPreds.head

  private val emptyHeapTerm = {
    import IExpression._
    heapPair(emptyArray, 0)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The sort of heaps.
   */
  object HeapSort extends ProxySort(rawHeapSort) with Theory.TheorySort {
    import IExpression._

    override def individuals : Stream[ITerm] = elementLists

    private lazy val elementLists : Stream[ITerm] =
      emptyHeap() #::
      (for (heap <- elementLists; obj <- ObjectSort.individuals)
       yield allocResHeap(alloc(heap, obj)))

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      rawHeapSort.augmentModelTermSet(model, terms, allTerms, definedTerms)

      val toRemove = new ArrayBuffer[(IdealInt, Sort)]

      for ((oldkey@(id, `rawHeapSort`),
            IFunApp(`heapPair`,
                    Seq(contents, IIntLit(IdealInt(sizeInt))))) <- terms) {
        val contentsAr = new Array[ITerm] (sizeInt)

        var t = contents
        var cont = true
        while (cont) t match {
          case IFunApp(ExtArray.Store(_), Seq(t2, IIntLit(IdealInt(p)), v)) => {
            t = t2
            if (1 <= p && p <= contentsAr.size)
              contentsAr(p - 1) = v
          }
          case IFunApp(ExtArray.Const(_), Seq(v)) => {
            for (n <- 0 until contentsAr.size)
              if (contentsAr(n) == null)
                contentsAr(n) = v
            cont = false
          }
        }

        val constrTerm =
          contentsAr.foldLeft(emptyHeap()) {
            case (heap, obj) => allocResHeap(alloc(heap, obj)) }

        terms.put((id, this), constrTerm)
        toRemove += oldkey
      }

      terms --= toRemove
    }

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get (d, this)

    val theory = ArrayHeap.this
  }

  override val dependencies = List(offHeapADT, arrayTheory, onHeapADT)

  //////////////////////////////////////////////////////////////////////////////

  private val OSo     = ObjectSort
  private val HSo     = HeapSort
  private val ASo     = AddressSort
  private val ARSo    = AddressRangeSort
  private val AResSo  = AllocResSort
  private val BAResSo = BatchAllocResSort

  val emptyHeap =
    new MonoSortedIFunction("empty" + heapSortName, List(), HSo, true, false)
  val alloc =
    new MonoSortedIFunction("alloc", List(HSo, OSo), AResSo, true, false)
  val batchAlloc =
    new MonoSortedIFunction("batchAlloc", List(HSo, OSo, Integer), BAResSo,
                            true, false)
  val read =
    new MonoSortedIFunction("read", List(HSo, ASo), OSo, true, false)
  val readUnsafe =
    new MonoSortedIFunction("readUnsafe", List(HSo, ASo), OSo, true, false)
  val write =
    new MonoSortedIFunction("write", List(HSo, ASo, OSo), HSo, true, false)
  val batchWrite =
    new MonoSortedIFunction("batchWrite", List(HSo, ARSo, OSo), HSo,
                            true, false)
  val valid =
    new MonoSortedPredicate("valid", List(HSo, ASo))
  val addressRangeNth =
    new MonoSortedIFunction("addressRangeNth", List(ARSo, Integer), ASo,
                            true, false)
  val addressRangeWithin =
    new MonoSortedPredicate("addressRangeWithin", List(ARSo, ASo))

  val storeRange =
    new MonoSortedIFunction("storeRange",
                            List(ArraySort, Integer, Integer, OSo),
                            ArraySort, true, true)
  val distinctHeaps =
    new MonoSortedPredicate("distinctHeaps", List(HSo, HSo))

  //////////////////////////////////////////////////////////////////////////////

  val allAxioms : IFormula = {
    import IExpression._
    import arrayTheory.{select, store}

    // TODO: the first axiom ensures bidirectional propagation and is needed
    // for completeness, but is also very inefficient. Implement this axiom
    // using a plugin instead?

/*    ArraySort.all((heapAr, resultAr) =>
      Integer.all((start, end) =>
        ObjectSort.all(obj =>
          ITrigger(
            List(storeRange(heapAr, start, end, obj)),
            (resultAr === storeRange(heapAr, start, end, obj)) ==>
            ite(start < end,
                resultAr ===
                  store(storeRange(heapAr, start + 1, end, obj), start, obj),
                resultAr === heapAr))))) & */
    //
    ArraySort.all((heapAr) =>
      Integer.all((start, end, ind) =>
        ObjectSort.all((obj, result) =>
          ITrigger(
            List(select(storeRange(heapAr, start, end, obj), ind)),
            (result ===
              select(storeRange(heapAr, start, end, obj), ind)) ==>
            (result ===
              ite((start <= ind) & (ind < end), obj, select(heapAr, ind))))))) &
    //
    HeapSort.all((heap1, heap2) =>
      distinctHeaps(heap1, heap2) ==>
        ((heapSize(heap1) =/= heapSize(heap2)) |
         Integer.ex(ind =>
           (0 < ind) & (ind <= heapSize(heap1)) &
           (select(heapContents(heap1), ind) =/=
            select(heapContents(heap2), ind))))
    )
  }

  val functions =
    List(emptyHeap, alloc, batchAlloc, read, readUnsafe, write, batchWrite,
         addressRangeNth, storeRange)
  val predefPredicates =
    List(valid, addressRangeWithin, distinctHeaps)

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms    = allAxioms,
                     otherTheories   = dependencies,
                     extraPredicates = predefPredicates)

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))
  val functionalPredicates =
    (functions map funPredMap).toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  private val pluginObj = new Plugin {
    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      goalState(goal) match {
        case Plugin.GoalState.Eager =>
          List()
        case Plugin.GoalState.Intermediate =>
          expandExtensionality(goal)
        case Plugin.GoalState.Final =>
          List()
      }
  }

  def plugin = Some(pluginObj)

  /**
   * The extensionality axiom is implemented by rewriting negated
   * equations about heaps.
   */
  private def expandExtensionality(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts

    if (!facts.arithConj.negativeEqs.isTrue) {
      val predConj   = facts.predConj
      val heapConsts = new MHashSet[ConstantTerm]

      for (a <- predConj.positiveLitsWithPred(_heapPair))
        heapConsts ++= a.last.constants

      if (!heapConsts.isEmpty) {
        implicit val order = goal.order
        import TerForConvenience._

        val eqs =
          Plugin.findDistinctConstants(heapConsts.toSet, goal)

        for ((c, d) <- eqs;
             axiom <- List(
               Plugin.AddAxiom(List(c =/= d),
                               distinctHeaps(List(l(c), l(d))),
                               ArrayHeap.this),
               Plugin.RemoveFacts(c =/= d)
             )) yield axiom
      } else {
        List()
      }
    } else {
      List()
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor called during pre-processing to eliminate symbols.
   */
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._
    import arrayTheory.{select, store}

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {

      case IFunApp(`emptyHeap`, _) =>
        emptyHeapTerm

      case IFunApp(`read`, _) => {
        val heap  = subres(0).asInstanceOf[ITerm]
        val addr  = subres(1).asInstanceOf[ITerm]
        val saddr = shiftVars(addr, 0, 1)
/*        withEps(heap, ObjectSort, (cont, size) =>
	        ite(validTest2(size, addr),
              select(cont, addrOrd(addr)),
              defaultObject)) */
        withEps3(heap, ObjectSort, (cont, size, result) =>
          ex(
            ((saddr === nthAddr(v(0))) & (v(0) >= 1) & (v(0) <= size) &
             (result === select(cont, v(0)))) |
            ((saddr === nthAddr(v(0))) & (v(0) <= 0 | v(0) > size) &
             (result === defaultObject)) |
            ((saddr === Null) &
             (result === defaultObject))
          ))
      }

      case IFunApp(`readUnsafe`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val addr = subres(1).asInstanceOf[ITerm]
        withEps(heap, ObjectSort, (cont, size) =>
          select(cont, addrOrd(addr)))
      }

      case IFunApp(`write`, _) => {
        val heap  = subres(0).asInstanceOf[ITerm]
        val addr  = subres(1).asInstanceOf[ITerm]
        val obj   = subres(2).asInstanceOf[ITerm]
        val saddr = shiftVars(addr, 0, 1)
        val sobj  = shiftVars(obj, 0, 1)
        withEps2(heap, (cont, size, cont2, size2) =>
          ex(
            (size === size2) &
            (((saddr === nthAddr(v(0))) & (v(0) >= 1 & v(0) <= size) &
              (cont2 === store(cont, v(0), sobj))) |
             ((saddr === nthAddr(v(0))) & (v(0) <= 0 | v(0) > size) &
              (cont2 === cont)) |
             ((saddr === Null) &
              (cont2 === cont)))
        ))
      }

      case IFunApp(`alloc`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val obj  = subres(1).asInstanceOf[ITerm]
        withEps(heap, AllocResSort, (cont, size) =>
	        allocResPair(heapPair(store(cont, size + 1, obj), size + 1),
	                     nthAddr(size + 1)))
      }

      case IFunApp(`batchAlloc`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val obj  = subres(1).asInstanceOf[ITerm]
        val num  = subres(2).asInstanceOf[ITerm]
        withEps(heap, AllocResSort, (cont, size) =>
          ite(num > 0,
	            batchAllocResPair(
                heapPair(
                  storeRange(cont, size + 1, size + 1 + num, obj), size + num),
	              nthAddrRange(size + 1, num)),
              batchAllocResPair(
                heap, nthAddrRange(1, 0))))
      }

      case IFunApp(`batchWrite`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val ar   = subres(1).asInstanceOf[ITerm]
        val obj  = subres(2).asInstanceOf[ITerm]
        withEps2(heap, (cont, size, cont2, size2) =>
          (size === size2) &
          (((addressRangeStart(ar) + addressRangeSize(ar) - 1 <= size) &
            (cont2 === storeRange(cont,
                                  addressRangeStart(ar),
                                  addressRangeStart(ar) + addressRangeSize(ar),
                                  obj))) |
           (!(addressRangeStart(ar) + addressRangeSize(ar) - 1 <= size) &
            (cont2 === cont)))
        )
      }

      case IFunApp(`nthAddr`, _) =>
        subres match {
          case Seq(Const(n)) if n >= 1 => {
            t update subres
          }
          case Seq(Const(_)) => {
            nullAddr()
          }
          case _ => {
            // TODO: this check has to happen in the parser
            Console.err.println(
              s"Warning: ${nthAddr.name} applied to non-constant " +
              s"argument ${subres(0)}")
            t update subres
          }
        }

      case IFunApp(`nthAddrRange`, _) =>
        subres match {
          case Seq(Const(n), Const(s)) if n >= 1 && s >= 0 => {
            t update subres
          }
          case Seq(Const(_), Const(_)) => {
            nthAddrRange(1, 0)
          }
          case _ => {
            // TODO: this check has to happen in the parser
            Console.err.println(
              s"Warning: ${nthAddrRange.name} applied to non-constant " +
              s"arguments ${subres.mkString(", ")}")
            t update subres
          }
        }

      case IFunApp(`addressRangeNth`, _) => {
        val range = subres(0).asInstanceOf[ITerm]
        val n     = subres(1).asInstanceOf[ITerm]
        // TODO: avoid duplicating terms
        ite((n >= 0) & (n < addressRangeSize(range)),
            nthAddr(addressRangeStart(range) + n),
            nullAddr())
      }

      case IAtom(`valid`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val addr = subres(1).asInstanceOf[ITerm]
//	ex((v(0) <= heapSize(shiftVars(heap, 0, 1))) &
//	   (nthAddr(v(0)) === shiftVars(addr, 0, 1)))
	      validTest(heap, addr)
      }

      case IAtom(`addressRangeWithin`, _) => {
        val ar   = subres(0).asInstanceOf[ITerm]
        val addr = subres(1).asInstanceOf[ITerm]
        // TODO: avoid duplicating terms
        (addr =/= nullAddr()) &
        (addressRangeStart(ar) <= addrOrd(addr)) &
        (addrOrd(addr) < addressRangeStart(ar) + addressRangeSize(ar))
      }

      case _ =>
        t update subres
    }

    private def validTest(heap : ITerm, p : ITerm) =
// TODO: avoid duplicating the p expression
      (p =/= nullAddr()) & (addrOrd(p) <= heapSize(heap))

    private def validTest2(size : ITerm, p : ITerm) =
// TODO: avoid duplicating the p expression
      (p =/= nullAddr()) & (addrOrd(p) <= size)

    private val contC = ArraySort newConstant "contC"
    private val sizeC = IExpression.Sort.Integer newConstant "sizeC"
    private val cont2C = ArraySort newConstant "cont2C"
    private val size2C = IExpression.Sort.Integer newConstant "size2C"

    private def withEps(heap    : ITerm,
                        resSort : Sort,
                        body    : (ITerm, ITerm) => ITerm) : ITerm =
      heap match {
        case SimpleTerm(heap) => {
	        body(heapContents(heap), heapSize(heap))
	      }
	      case heap => {
          val sheap = shiftVars(heap, 0, 3)
          val sbody = ConstantSubstVisitor(shiftVars(body(contC, sizeC), 0, 3),
                                           Map(contC -> v(1, ArraySort),
                                               sizeC -> v(0)))
          resSort.eps(ArraySort.ex(ex((heapPair(v(1, ArraySort), v(0)) === sheap) &
                                        (v(2, resSort) === sbody))))
        }
      }

    private def withEps2(heap : ITerm,
                         body : (ITerm, ITerm, ITerm, ITerm) => IFormula)
                               : ITerm = {
      val sheap = shiftVars(heap, 0, 5)
      val sbody = ConstantSubstVisitor(
                    shiftVars(body(contC, sizeC, cont2C, size2C), 0, 5),
                    Map(contC  -> v(1, ArraySort), sizeC  -> v(0),
                        cont2C -> v(3, ArraySort), size2C -> v(2)))
      HeapSort.eps(ArraySort.ex(ex(ArraySort.ex(ex(
        (heapPair(v(1, ArraySort), v(0)) === sheap) &
        (heapPair(v(3, ArraySort), v(2)) === v(4, HeapSort)) &
        sbody)))))
    }
  
    private def withEps3(heap    : ITerm,
                         resSort : Sort,
                         body    : (ITerm, ITerm, ITerm) => IFormula) : ITerm = {
      val resC  = resSort newConstant "result"
      val sheap = shiftVars(heap, 0, 3)
      val sbody = ConstantSubstVisitor(shiftVars(body(contC, sizeC, resC), 0, 3),
                                       Map(contC -> v(1, ArraySort),
                                           sizeC -> v(0),
                                           resC  -> v(2, resSort)))
        resSort.eps(ArraySort.ex(ex(
          (heapPair(v(1, ArraySort), v(0)) === sheap) & sbody)))
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

  private val Null = IFunApp(nullAddr, Seq())

  private type NullStatus  = Int
  private type AllocStatus = Int

  private val N_TOP       : NullStatus = 3
  private val N_NULL      : NullStatus = 2
  private val N_NON_NULL  : NullStatus = 1
  private val N_BOT       : NullStatus = 0

  private val A_TOP       : AllocStatus = 3
  private val A_ALLOC     : AllocStatus = 2
  private val A_NON_ALLOC : AllocStatus = 1
  private val A_BOT       : AllocStatus = 0

  private object ContradictionException extends Exception

  private case class AddrStatus(
    nullStatus  : Map[ITerm, NullStatus],
    allocStatus : Map[(ITerm, ITerm), AllocStatus]) {

    def meetNullStatus(addr : ITerm, s : NullStatus) : AddrStatus = {
      val oldS = nullStatus.getOrElse(addr, N_TOP)
      val newS = oldS & s
      if (newS == 0)
        throw ContradictionException
      if (oldS == newS)
        this
      else
        AddrStatus(nullStatus + (addr -> newS), allocStatus)
    }

    def meetAllocStatus(addr : ITerm, heap : ITerm,
                        s : AllocStatus) : AddrStatus = {
      val oldS = allocStatus.getOrElse((addr, heap), N_TOP)
      val newS = oldS & s
      if (newS == 0)
        throw ContradictionException
      if (oldS == newS)
        this
      else
        AddrStatus(nullStatus, allocStatus + ((addr, heap) -> newS))
    }

    def maybeNonNull(addr : ITerm) =
      (nullStatus.getOrElse(addr, N_TOP) & N_NON_NULL) != N_BOT

    def mustbeNull(addr : ITerm) = !maybeNonNull(addr)

    def maybeNull(addr : ITerm) =
      (nullStatus.getOrElse(addr, N_TOP) & N_NULL) != N_BOT

    def mustbeNonNull(addr : ITerm) = !maybeNull(addr)

    def maybeNonValid(addr : ITerm, heap : ITerm) =
      (allocStatus.getOrElse((addr, heap), A_TOP) & A_NON_ALLOC) != A_BOT

    def mustbeValid(addr : ITerm, heap : ITerm) = !maybeNonValid(addr, heap)

    def reduce : AddrStatus = {
      var changed = false
      def checkChanged(oldS : Int, newS : Int) : Int =
        if (oldS == newS) {
          oldS
        } else if (newS == 0) {
          throw ContradictionException
        } else {
          changed = true
          newS
        }

      val newAS =
        for (((addr, heap), oldS) <- allocStatus) yield {
          val newS = if (mustbeNull(addr)) oldS & ~A_ALLOC else oldS
          ((addr, heap), checkChanged(oldS, newS))
        }

      if (changed) AddrStatus(nullStatus, newAS) else this
    }

    def --(that : AddrStatus) : AddrStatus = {
      val nullDiff =
        for ((a, s) <- nullStatus; if s != that.nullStatus.getOrElse(s, N_TOP))
        yield (a -> s)
      val allocDiff =
        for ((p, s) <- allocStatus; if s != that.allocStatus.getOrElse(p, A_TOP))
        yield (p -> s)
      AddrStatus(nullDiff, allocDiff)
    }

    // TODO: make this function deterministic
    def toFormula : IFormula = {
      import IExpression._
      val validVars =
        (for (((a, _), A_ALLOC) <- allocStatus) yield a).toSet
      val f1 =
        and(for ((a, s) <- nullStatus; if s != N_TOP && !validVars(a))
            yield s match {
              case N_NULL     => a === Null
              case N_NON_NULL => a =/= Null
            })
      val f2 =
        and(for (((a, h), s) <- allocStatus; if s != A_TOP)
            yield s match {
              case A_ALLOC     => valid(h, a)
              case A_NON_ALLOC => !valid(h, a)
            })
      f1 &&& f2
    }

    lazy val simplifier = {
      val heapSimp = heapSimplify(this) _
      new Simplifier {
        protected override def furtherSimplifications(e : IExpression) =
          heapSimp(e)
      }
    }
  }

  private def runValidityInference(
    constraints   : Seq[IFormula],
    initialStatus : AddrStatus) : (AddrStatus, Seq[IFormula]) = {
    
    import IExpression._

    var status = initialStatus

    val remainingConstraints = constraints.flatMap(c =>
      c match {
        case Eq(Null, a) => {
          status = status.meetNullStatus(a, N_NULL)
          List()
        }
        case Eq(a, Null) => {
          status = status.meetNullStatus(a, N_NULL)
          List()
        }
        case INot(Eq(Null, a)) => {
          status = status.meetNullStatus(a, N_NON_NULL)
          List()
        }
        case INot(Eq(a, Null)) => {
          status = status.meetNullStatus(a, N_NON_NULL)
          List()
        }
        case Eq(IFunApp(`nthAddr`, Seq(_)), a) => {
          status = status.meetNullStatus(a, ~N_NULL)
          List(c)
        }
        case IExpression.EqLit(
               IFunApp(ADT.CtorId(`onHeapADT`, `addressSortId`), Seq(a)),
               IdealInt.ZERO) => {
          status = status.meetNullStatus(a, ~N_NON_NULL)
          List()
        }
        case IExpression.EqLit(
               IFunApp(ADT.CtorId(`onHeapADT`, `addressSortId`), Seq(a)),
               IdealInt.ONE) => {
          status = status.meetNullStatus(a, ~N_NULL)
          List()
        }
        case DiffBound(IFunApp(`heapSize`, Seq(h)),
                       IFunApp(`addrOrd`, Seq(a)),
                       n)
            if n.signum >= 0 && status.mustbeNonNull(a) => {
          status = status.meetAllocStatus(a, h, A_ALLOC)
          List(c)
        }
        case DiffBound(IFunApp(`addrOrd`, Seq(a)),
                       IFunApp(`heapSize`, Seq(h)),
                       n)
            if n.signum > 0 => {
          status = status.meetAllocStatus(a, h, A_NON_ALLOC)
          List(c)
        }
        case c => {
          //println(s"Not handled: $c under $status")
          List(c)
        }
      })

    status = status.reduce

    if (status == initialStatus)
      (initialStatus, remainingConstraints)
    else
      runValidityInference(remainingConstraints, status)
  }

  private def heapSimplify(addrStatus : AddrStatus)
                          (e : IExpression) : IExpression = {
    import IExpression._
    import arrayTheory.{select}
    e match {
      case Geq(Const(n), IFunApp(`addrOrd`, _)) if n.signum <= 0 =>
        false
      case Geq(IFunApp(`addrOrd`, _), Const(n)) if n.signum > 0 =>
        true
      case IFunApp(`nthAddr`, Seq(IFunApp(`addrOrd`, Seq(a))))
          if addrStatus.mustbeNonNull(a) =>
        a
      case Eq(IFunApp(`addrOrd`, Seq(a)), IFunApp(`addrOrd`, Seq(a2)))
          if addrStatus.mustbeNonNull(a) && addrStatus.mustbeNonNull(a2) =>
        a === a2
      case DiffBound(IFunApp(`heapSize`, Seq(h)),
                     IFunApp(`addrOrd`, Seq(a)),
                     n)
          if n.signum >= 0 && addrStatus.mustbeValid(a, h) =>
        true
      case DiffBound(IFunApp(`addrOrd`, Seq(a)),
                     IFunApp(`heapSize`, Seq(h)),
                     n)
          if n.signum > 0 && addrStatus.mustbeValid(a, h) =>
        false
      case IFunApp(`select`,
                   Seq(IFunApp(`heapContents`, Seq(h)),
                       IFunApp(`addrOrd`, Seq(a))))
          if addrStatus.mustbeValid(a, h) =>
        read(h, a)
      case IFunApp(`select`,
                   Seq(IFunApp(`heapContents`, Seq(h)),
                       IFunApp(`addrOrd`, Seq(a)))) =>
        readUnsafe(h, a)
      case e =>
        e
    }
  }

  private def simplifyFor(f          : IFormula,
                          addrStatus : AddrStatus) : IFormula =
    f match {
      case IBinFormula(j@IBinJunctor.And, _, _) => {
        import IExpression._
        val conjuncts = LineariseVisitor(f, j)
        val (other, constraints) =
          conjuncts.partition(_.isInstanceOf[IBinFormula])
        val (newAddrStatus, other2) =
          runValidityInference(constraints, addrStatus)
        val other3 =
          (other ++ other2).map(simplifyFor(_, newAddrStatus))

        newAddrStatus.toFormula &&& and(other3)
      }
      case IBinFormula(j@IBinJunctor.Or, _, _) => {
        import IExpression._
        val conjuncts = LineariseVisitor(f, j)
        val (other, constraints) =
          conjuncts.partition(_.isInstanceOf[IBinFormula])
        val constraints2 = constraints.map(~_)
        val (newAddrStatus, other2) =
          runValidityInference(constraints2, addrStatus)
        val other3 = other2.map(~_)
        val other4 = (other ++ other3).map(simplifyFor(_, newAddrStatus))

        newAddrStatus.toFormula ===> or(other4)
      }
      case _ =>
        addrStatus.simplifier(f)
    }

  override def iPostprocess(f : IFormula, signature : Signature) : IFormula = {
    val simp = new Simplifier
    simplifyFor(simp(f), AddrStatus(Map(), Map()))
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

  override def toString = name
  TheoryRegistry register this
  IHeap register this

}
