/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2025 Philipp Ruemmer <ph_r@gmx.net>
 *               2020-2023 Zafer Esen <zafer.esen@gmail.com>
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

import ap.theories.{Theory, ADT, TheoryRegistry}
import ap.basetypes._
import ap.parser.IExpression.Predicate
import ap.parser._
import ap.theories.ADT.ADTProxySort
import ap.types._
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, Map => MMap,
                                 Set => MSet}
import scala.collection.{mutable, Map => GMap}

object NativeHeap {
  private val AC = Debug.AC_HEAP
  
  class HeapException(m : String) extends Exception(m)

  class AddressSort(sortName : String,
                    val heapTheory : NativeHeap) extends ProxySort(Sort.Nat)
                                           with Theory.TheorySort {
    import IExpression.toFunApplier

    override val name = sortName
    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(heapTheory.nthAddr(d.intValue))   // TODO: correctly use nullAddr!

    override lazy val individuals : Stream[ITerm] =
      for (t <- Sort.Nat.individuals) yield heapTheory.nthAddr(t)

    val theory = heapTheory
  }

  class HeapSort(sortName : String,
                 val heapTheory : NativeHeap) extends ProxySort(Sort.Integer)
                                        with Theory.TheorySort {
    import IExpression.toFunApplier
    import ap.terfor.conjunctions.Conjunction
    import ap.terfor.preds.Atom
    import heapTheory.{ObjectSort, alloc, emptyHeap, newHeap}
    override val name = sortName

    val theory = heapTheory

    override lazy val individuals : Stream[ITerm] =
      emptyHeap() #:: (for (t <- individuals;
                            obj <- ObjectSort.individuals)
        yield newHeap(alloc(t, obj)))

    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      assignment get ((d, this))
    }

    override def augmentModelTermSet(
                 model : Conjunction,
                 terms : MMap[(IdealInt, Sort), ITerm],
                 allTerms : Set[(IdealInt, Sort)],
                 definedTerms : MSet[(IdealInt, Sort)]) : Unit = {

      /** Helper functions to collect atoms from theory functions */
      def getAtoms (f : IFunction) : IndexedSeq[Atom] =
        model.predConj positiveLitsWithPred heapTheory.heapFunPredMap(f)
      def getHeapADTAtoms (f : IFunction) : IndexedSeq[Atom] =
        model.predConj positiveLitsWithPred heapTheory.heapADTs.
          functionPredicateMapping.find(_._1 == f).get._2

      /* Collect the relevant functions and predicates of the theory */
      import heapTheory.{counter, emptyHeap, read, write, allocHeap,
                         batchAllocHeap, batchWrite,
                         addrRangeStart, addrRangeSize}
      val writeAtoms = getAtoms(write)
      val allocAtoms = getAtoms(allocHeap)
      val batchAllocAtoms = getAtoms(batchAllocHeap)
      val batchWriteAtoms = getAtoms(batchWrite)
      val addrRangeStartAtoms = getHeapADTAtoms(addrRangeStart)
      val addrRangeSizeAtoms = getHeapADTAtoms(addrRangeSize)
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)

      import IExpression.{i, toFunApplier}

      def createHeapTerm(contents : Seq[IdealInt]) : ITerm = {
        assume(contents.nonEmpty) // emptyHeap should be handled separately
        import heapTheory.{newHeap, alloc, newBatchHeap, batchAlloc}
        var currentTerm = emptyHeap()

        /* below code tries to group objects by indices, in order to
        * compact the produced model by making use of batchAllocHeap*/
        var change = true
        var l = contents.zipWithIndex.map(c => (c._1, Set(c._2)))
        while(change) {
          change = false
          val res = l.zipWithIndex.map(c => {
            val thisElem = c._1
            if (c._2 > 0) {
              val prevElem = l(c._2 - 1)
              if (thisElem._1 == prevElem._1) {
                (thisElem._1, prevElem._2 ++ thisElem._2)
              } else {
                thisElem
              }
            } else {
              thisElem
            }
          }
          )
          if (l.zipWithIndex.exists(a => a._1 != res(a._2)))
            change = true
          l = res
        }
        val groupedContents = (l.foldLeft(List(l.head))((a, b) =>
          if (a.head._1 == b._1)
            List(b) ++ a.tail
          else
            List(b) ++ a)).sortBy(e => e._2.min)

        for ((objTermId, indices) <- groupedContents) {
          val objTerm = terms.getOrElse((objTermId, heapTheory.ObjectSort),
            heapTheory._defObj)
          val n = indices.size // n = object repeat count
          if (n > 1) {
            currentTerm = newBatchHeap(batchAlloc(currentTerm, objTerm, n))
          } else {
            currentTerm = newHeap(alloc(currentTerm, objTerm))
          }
        }
// todo:use only official functions of the theory in the models
        /*import heapTheory.{_defObj, alloc, newHeap}
        for (objTermId <- contents) {
          val objTerm = terms.getOrElse((objTermId, heapTheory.ObjectSort),
            heapTheory._defObj)
          currentTerm = newHeap(alloc(currentTerm, objTerm))
        }*/
        currentTerm
      }

      val heapContents = new MHashMap[IdealInt, ArrayBuffer[IdealInt]] //[eh->[],h1:[1,2],...]

      // fill in the contents for empty heaps
      for (a <- emptyHeapAtoms) { // emptyHeap(heapId)
          heapContents += ((a(0).constant, new ArrayBuffer[IdealInt](0)))
      }

      // Map[addrRange(addrRangeId -> (addRangeStartId : IdealInt,
      //                               addrRangeSize : Int))]
      val addrRangeInfo =
        (for (addrRangeSizePair <- (addrRangeStartAtoms.sortBy(_(0).constant.intValue) zip
        addrRangeSizeAtoms.sortBy(_(0).constant.intValue))) yield {
        val addrRangeId = addrRangeSizePair._1(0).constant
        assert (addrRangeId == addrRangeSizePair._2(0).constant)
        (addrRangeId, (addrRangeSizePair._1(1).constant,
          addrRangeSizePair._2(1).constant.intValue))
      }).toMap

      // initialize content buffers of non-empty heaps
      // counter(heapId, counterVal)
      for (a <- counterAtoms if a(1).constant.intValue > 0) {
        val heapId = a(0).constant
        val counterVal = a(1).constant
        val contentBuffer = new ArrayBuffer[IdealInt](counterVal.intValue)
        for (_ <- 0 until counterVal.intValue)
          contentBuffer += -1
        heapContents += ((heapId,contentBuffer))
      }

      var somethingChanged = true
      // iterate over non-empty heaps to fixed-point
      while(somethingChanged) {
        somethingChanged = false
        for (a <- counterAtoms if a(1).constant.intValue > 0) {
          val heapId = a(0).constant
          val counterVal = a(1).constant
          /*
        * A heap is either created through an (batch)alloc, or through a write.
        * If it is created through alloc, all locations except the last location
        * (i.e., counterVal), are the same as the original heap.
        * If it is craeted through batchAlloc, all locations except the last n
        * locations are the same as the original heap, where n is the batch size.
        * If it is created through write, all locations except the written
        * location, are the same as the original heap.
        */

          // batchAllocHeap(prevHeapId, obj, n, heapId)
          val (prevHeapId, changedAddr, newObj, allocOrWriteFound, changeSize) =
            batchAllocAtoms.find(p => p(3).constant == heapId) match {
              case Some(p) =>
                (p(0).constant, counterVal, p(1).constant, true, p(2).constant.intValue)
              case None =>
                // allocHeap(prevHeapId, obj, heapId)
                allocAtoms.find(p => p(2).constant == heapId) match {
                  case Some(p) =>
                    (p(0).constant, counterVal, p(1).constant, true, 1)
                  case None => // no allocs found, then there must be a write
                    // write(prevHeapId, addr, obj, heapId)
                    writeAtoms.find(p => p(3).constant == heapId) match {
                      case Some(p) =>
                        (p(0).constant, p(1).constant, p(2).constant, true, 1)
                      case None =>
                        // batchWrite(prevHeapId, addrRange, obj, heapId)
                        batchWriteAtoms find (p =>
                          p(3).constant == heapId) match {
                          case Some (p) =>
                            val (addrRangeStart, addrRangeSize) =
                              addrRangeInfo.getOrElse(p(1).constant, (IdealInt(-1), 0))
                            (p(0).constant, // prevHeapID
                              addrRangeStart + addrRangeSize - 1, // last changed address
                              p(2).constant, // object
                              addrRangeStart != IdealInt(-1), // false if addrStart could not be determined
                              addrRangeSize) // size of change
                          case None => // no allocs or writes found
                            (IdealInt(-1), IdealInt(-1), IdealInt(-1), false, 0)
                      }
                    }
                }
            }

          if (prevHeapId != heapId) {
            if (allocOrWriteFound) {
              // copy all locations from previous heap, then update changed loc
              // enumerate changed indices (changedAddr points to the last changed addr)
              val changedInds =
                (changedAddr.intValue - changeSize) until changedAddr.intValue
              if (heapContents contains prevHeapId) { // otherwise prevHeap is the empty heap
                // todo: what about write that doesn't change heap size?
                val prevHeap = heapContents(prevHeapId)
                // todo: if prevHeap is unknown this will crash! use nondet values
                for (i <- prevHeap.indices if !changedInds.contains(i)) {
                  if (heapContents(heapId)(i) != prevHeap(i)) {
                    somethingChanged = true
                    heapContents(heapId)(i) = prevHeap(i)
                  }
                }
              }
              for(changedInd <- changedInds) {
                if(heapContents(heapId)(changedInd) != newObj)
                  somethingChanged = true
                heapContents(heapId)(changedInd) = newObj // this does not depend on prev heaps.
              }
            } else { // try to find the contents through read atoms
              for (a <- readAtoms if a(0).constant == heapId) {
                val changedInd = a(1).constant.intValue - 1
                val newVal = a(2).constant
               // ignoring read atoms outside this heap term's allocated range
               // these reads would only be defObj
                if (heapContents(heapId).length > changedInd &&
                    changedInd >= 0 &&
                    heapContents(heapId)(changedInd) != newVal) {
                  heapContents(heapId)(changedInd) = newVal
                  somethingChanged = true
                }
              }
            }
          }
        }
      }

      // define emptyHeap terms
      for (a <- emptyHeapAtoms) {
        val heapKey = (a(0).constant, this)
        if (!(definedTerms contains heapKey)) {
          terms.put(heapKey, emptyHeap())
          definedTerms += heapKey
        }
      }

      // define rest of the heap terms
      for (a <- counterAtoms if a(1).constant.intValue > 0) {
        val heapId = a(0).constant
        val heapKey = (heapId, this)

        // if one of the object terms has not been yet defined, return
        for (id <- heapContents(heapId))
          if ((allTerms exists (key => key._1 == id)) &&
              !(terms exists (term => term._1._1 == id)))
            return

        val heapTerm = createHeapTerm(heapContents(heapId))
        if (!(definedTerms contains heapKey) || //if this term is not defined
            (terms(heapKey) != heapTerm)) { // or has changed
          terms.put(heapKey, heapTerm) //update the heap term
          if (!(definedTerms contains heapKey)) definedTerms += heapKey
        }
      }
    }
  }
/*
  // heap theory hard-coded ADT sorts, ctors and functions
  allocResSort     : allocResCtor(heap X addr); newHeap, newAddr
  batchAllocResSort: batchAllocResCtor (heap X addrRange); newBatchHeap, newAddrRange
  addressRangeSort : addressRangeCtor (addr X nat); addrRangeStart, addrRangeSize
  */
  object HeapSortExtractor {
    def unapply (sort : Sort) : Option[NativeHeap] = {
      sort match {
        case address : NativeHeap.AddressSort =>
          Some(address.heapTheory)
        case adtSort : ADTProxySort =>
          // check if this is one of the hard-coded heapADT sorts
          // this extractor depends on a few assumptions:
          //   1. current hard-coded ADTs have all two arguments and
          //   2. the hard-coded ADTs are declared last
          val ctors = adtSort.adtTheory.constructors.filter(ctor =>
            ctor.resSort == adtSort && ctor.argSorts.size == 2)
          if (ctors isEmpty)
            None
          else {
            val ctor = ctors.last
            ctor.argSorts match {
              case Seq(h: HeapSort, _) if // allocRes(heap, object)
              Seq(h.heapTheory.allocResCtor, h.heapTheory.batchAllocResCtor)
                contains ctor => Some(h.heapTheory) // alloc
              case Seq(a: AddressSort, _) // addrRange(addr, nat)
                if ctor == a.heapTheory.addressRangeCtor =>
                Some(a.heapTheory)
              case _ => None
            }
          }
        case _ => None
      }
    }
  }

  /**
   * Extractor recognising the functions of any Heap theory.
   * Also recognises the selectors and the constructor of AllocResSort ADT
   */
  object HeapFunExtractor {
    def unapply(fun: IFunction): Option[NativeHeap] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t: NativeHeap) => Some(t)
        case Some(_: ADT) if fun.isInstanceOf[MonoSortedIFunction] =>
          val sortedFun = fun.asInstanceOf[MonoSortedIFunction]
          sortedFun.resSort match {
            case s: NativeHeap.HeapSort =>
              if (sortedFun == s.heapTheory.newHeap) // newHeap(ar : AllocRes)
                Some(s.heapTheory)
              else None
            case s: NativeHeap.AddressSort =>
              if (sortedFun == s.heapTheory.newAddr) // newAddr(ar : AllocRes)
                Some(s.heapTheory)
              else None
            case t if sortedFun.arity == 2 => // AllocRes constructor
              sortedFun.argSorts.head match {
                case s: NativeHeap.HeapSort =>
                  if (t == s.heapTheory.allocResSort)
                    Some(s.heapTheory)
                  else None
                case _ => None
              }
              //todo: support new functions of the theory: newBatchHeap, newAddrRange etc.
            case _ => None
          }
        case _ => None
      }
  }

  /**
   * Extractor recognising the predicates of any Heap theory.
   */
  object HeapPredExtractor {
    def unapply(pred : Predicate) : Option[NativeHeap] =
      (TheoryRegistry lookupSymbol pred) match {
        case Some(t : NativeHeap) => Some(t)
        case _ => None
      }
  }
}

/**
 * defaultObjectCtor is called from the theory (before it is completely
 * initialised), and it passes back the theory ADTs for adding to environment
 * (e.g. as done in SMTParser2InputAbsy), and also the actual constructors
 * for the ctorSignatures, so the defObj term can be built using those.
 *
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param sortNames
 * @param ctorSignatures
 */
class NativeHeap(heapSortName : String, addressSortName : String,
           addressRangeSortName : String,
           objectSort : Heap.ADTSort, sortNames : Seq[String],
           ctorSignatures : Seq[(String, Heap.CtorSignature)],
           defaultObjectCtor : Seq[MonoSortedIFunction] => ITerm)
    extends Heap with SMTLinearisableTheory {

  import NativeHeap._
  import Heap._

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC,
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case ADTSort(id) => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
          case AddrSort | AddrRangeSort => true
        }
    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  val AddressSort = new AddressSort(addressSortName, this)
  val HeapSort = new HeapSort(heapSortName, this)
  val emptyHeap = new MonoSortedIFunction("empty" + heapSortName,
    argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)

  val nthAddr = new MonoSortedIFunction("nth" + addressSortName,
    List(Sort.Nat), AddressSort, false, false)
  val nextAddr =
    new MonoSortedIFunction("next" + addressSortName,
    List(HeapSort, Sort.Integer), AddressSort, false, false)

  object HeapADTSortId extends Enumeration(initial = sortNames.size) {
    type HeapADTSortId = Value
    val allocResSortId, batchAllocResSortId, addressRangeSortId = Value
  }
  import HeapADTSortId._

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort      => ADT.ADTSort(t.num)
      case t : OtherSort    => ADT.OtherSort(t.sort)
      case AddrSort         => ADT.OtherSort(AddressSort)
      case AddrRangeSort    => ADT.ADTSort(addressRangeSortId)
    }

  private implicit def HeapSortToADTSort(l : Seq[(String, CtorSignature)]):
  Seq[(String, ADT.CtorSignature)] = {
    for (s <- l) yield (s._1, ADT.CtorSignature(
      for (arg <- s._2.arguments) yield (arg._1, HeapSortToADTSort(arg._2)),
      ADT.ADTSort(s._2.result.num)))
  }

  implicit def HeapADTSortIdToInt(id : HeapADTSortId) : Int = id.id
  val objectSortId : Int = objectSort.num

  /** Create return sort of alloc as an ADT: Heap x Address */
  private val allocResCtorSignature = ADT.CtorSignature(
    List(("new" + heapSortName, ADT.OtherSort(HeapSort)),
      ("new" + addressSortName, ADT.OtherSort(AddressSort))),
    ADT.ADTSort(allocResSortId))

  /** Create AddressRange ADT returned by batchAlloc: start x size */
  private val addressRangeCtorSignature = ADT.CtorSignature(
    List((addressRangeSortName + "Start", ADT.OtherSort(AddressSort)),
      (addressRangeSortName + "Size", ADT.OtherSort(Sort.Nat))),
    ADT.ADTSort(addressRangeSortId))
  /** Create return sort of batchAlloc as an ADT: Heap x AddressRange */
  private val BatchAllocResCtorSignature = ADT.CtorSignature(
    List(("newBatch" + heapSortName, ADT.OtherSort(HeapSort)),
      ("new" + addressRangeSortName, ADT.ADTSort(addressRangeSortId))),
    ADT.ADTSort(batchAllocResSortId))

  // warning: heap ADTs must be declared last!
  // Also if any new heap ADT is added here, the sort extractor must be
  //   extended!
  val heapADTDefinitions : Map[HeapADTSortId, (String, ADT.CtorSignature)] = Map(
    (allocResSortId, ("AllocRes" + heapSortName, allocResCtorSignature)),
    (batchAllocResSortId, ("BatchAllocRes" + heapSortName, // BatchAllocRes
                       BatchAllocResCtorSignature)),
    (addressRangeSortId, (addressRangeSortName,            // AddressRange
                      addressRangeCtorSignature))
  )

  val userSortNames : Seq[String] = sortNames
  val userCtorSignatures : Seq[(String, CtorSignature)] = ctorSignatures
  val adtCtorSignatures = HeapSortToADTSort(userCtorSignatures)

  // We must avoid circular dependencies, therefore the ADT is
  // declared to depend on theories needed for the ADT sorts, but not
  // on the heap theory itself.
  val adtDependencies =
    (for ((_, sig) <- adtCtorSignatures;
          t <- sig.sortDependencies;
          if t != this)
     yield t).distinct

  val heapADTs : ADT = new ADT(
    userSortNames ++ //Object ADT and other input ADTs are defined first
      heapADTDefinitions.values.map(_._1), // names from theory declared ADTs
    adtCtorSignatures ++ // Object and other input ADT signatures
      heapADTDefinitions.values.toSeq, // signatures of theory declared ADTs
    overrideDeps = Some(adtDependencies)
  )

  val ObjectSort : Sort = heapADTs.sorts(objectSortId)
  val userADTSorts = heapADTs.sorts.take(sortNames.size)

  private val userADTIndsCtorsAndSels = // : Map[Sort, Seq[MonoSortedIFunction]] =
    (for ((sort, ind) <- userADTSorts.zipWithIndex) yield {
      for (id <- heapADTs.ctorIdsPerSort(ind)) yield {
        (id, heapADTs.constructors(id), heapADTs.selectors(id))
      }
    }).flatten.sortBy(triplet => triplet._1).unzip3
  val userADTCtors : Seq[MonoSortedIFunction] = userADTIndsCtorsAndSels._2
  val userADTSels : Seq[Seq[MonoSortedIFunction]] = userADTIndsCtorsAndSels._3

  val userHeapSorts = userADTSorts
  def hasUserHeapCtor(t : ITerm, id : Int) : IFormula = heapADTs.hasCtor(t, id)
  val userHeapConstructors = heapADTs.constructors.take(userADTCtors.size)
  val userHeapSelectors = heapADTs.selectors.take(userADTCtors.size)
  val userHeapUpdators = heapADTs.updators.take(userADTCtors.size)
  val userHeapCtorSignatures = ctorSignatures

  private val theoryADTSorts = heapADTs.sorts.drop(sortNames.size)
  private val theoryADTCtors = heapADTs.constructors.drop(userADTCtors.size)
  private val theoryADTSels  = heapADTs.selectors.drop(userADTCtors.size)

  val allocResSort      = theoryADTSorts(allocResSortId-sortNames.size)
  val allocResCtor      = theoryADTCtors(allocResSortId-sortNames.size)
  val newHeap           = theoryADTSels(allocResSortId-sortNames.size)(0)
  val newAddr           = theoryADTSels(allocResSortId-sortNames.size)(1)

  val batchAllocResSort = theoryADTSorts(batchAllocResSortId-sortNames.size)
  val batchAllocResCtor = theoryADTCtors(batchAllocResSortId-sortNames.size)
  val newBatchHeap      = theoryADTSels(batchAllocResSortId-sortNames.size)(0)
  val newAddrRange      = theoryADTSels(batchAllocResSortId-sortNames.size)(1)

  val addressRangeSort  = theoryADTSorts(addressRangeSortId-sortNames.size)
  val addressRangeCtor  = theoryADTCtors(addressRangeSortId-sortNames.size)
  val addrRangeStart    = theoryADTSels(addressRangeSortId-sortNames.size)(0)
  val addrRangeSize     = theoryADTSels(addressRangeSortId-sortNames.size)(1)

  val addressRangeSize = addrRangeSize

  val AddressRangeSort   = addressRangeSort
  val AllocResSort       = allocResSort
  val BatchAllocResSort  = batchAllocResSort
  val allocResAddr       = newAddr
  val allocResHeap       = newHeap
  val batchAllocResAddr  = newAddrRange
  val batchAllocResHeap  = newBatchHeap

  val nthAddrRange = new MonoSortedIFunction(s"nth${addressSortName}Range",
    List(Sort.Nat, Sort.Nat), addressRangeSort, false, false)

  val nth = new MonoSortedIFunction("nth" + addressRangeSortName,
    List(addressRangeSort, Sort.Nat), AddressSort,
    false, false)
  val within = new MonoSortedPredicate("within",
    List(addressRangeSort, AddressSort))

  val addressRangeNth = nth
  val addressRangeWithin = within

  /** Returns whether (an ADT) sort is declared as part of this theory. */
  def containsADTSort(sort : Sort): Boolean = theoryADTSorts.contains(sort)

  /** Functions and predicates of the theory
   * Assuming Address as address sort name, Heap as heap sort name, and
   * Obj as the selected object sort.
   * Some function / predicate names incorporate the defined / selected names.
   * ***************************************************************************
   * Public functions and predicates
   * ***************************************************************************
   * emptyHeap            : ()                   --> Heap
   * alloc                : Heap x Obj           --> Heap x Address (allocResHeap)
   * read                 : Heap x Address       --> Obj
   * write                : Heap x Address x Obj --> Heap
   * valid (isAlloc)      : Heap x Address       --> Bool
   * deAlloc              : Heap                 --> Heap
   * nthAddr              : Nat                  --> Address
   * nthAddrRange         : Nat x Nat            --> Address
   *
   * batchAlloc           : Heap x Obj   x Nat        --> Heap x AddressRange (batchAllocResHeap)
   * batchWrite           : Heap x AddressRange x Obj --> Heap
   * nth                  : AddressRange x Nat     --> Address
   * within               : AddressRange x Address --> Bool
   *
   *             0     1
   * writeADT : Obj x Obj --> Heap
   * * Updates the ADT's field (described by a read to 0) using value (1)
   * ***************************************************************************
   * Private functions and predicates
   * ***************************************************************************
   * counter  : Heap                 --> Nat
   *
   * * Below two functions are shorthand functions to get rid of allocRes ADT.
   * * They return a single value instead of the pair <Heap x Addr>.
   * * This also removes some quantifiers related to the ADT in the generated
   * * interpolants.
   * alloc<heapSortName>    : Heap x Obj           --> Heap
   * alloc<addressSortName> : Heap x Obj           --> Address
   *
   * * Below two functions are shorthand functions to get rid of batchAllocRes ADT.
   * * They return a single value instead of the pair <Heap x AddressRange>.
   * * This also removes some quantifiers related to the ADT in the generated
   * * interpolants.
   * batchAlloc<heapSortName>         : Heap x Obj x Nat --> Heap
   * batchAlloc<addressSortName>Range : Heap x Obj x Nat --> AddressRange
   * *
   * ***************************************************************************
   * */
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    allocResSort, false, false)
  val allocHeap = new MonoSortedIFunction("alloc" + heapSortName,
    List(HeapSort, ObjectSort), HeapSort, false, false)
  val allocAddr = new MonoSortedIFunction("alloc" + addressSortName,
    List(HeapSort, ObjectSort), AddressSort, false, false)
  val deAlloc = new MonoSortedIFunction("deAlloc", List(HeapSort),
    HeapSort, false, false)

  val batchAlloc = new MonoSortedIFunction("batchAlloc",
    List(HeapSort, ObjectSort, Sort.Nat), batchAllocResSort, false, false)
  val batchAllocHeap = new MonoSortedIFunction("batchAlloc" + heapSortName,
    List(HeapSort, ObjectSort, Sort.Nat), HeapSort, false, false)
  val batchAllocAddrRange =
    new MonoSortedIFunction("batchAlloc" + addressRangeSortName,
      List(HeapSort, ObjectSort, Sort.Nat), addressRangeSort, false, false)
  val batchWrite = new MonoSortedIFunction("batchWrite",
    List(HeapSort, addressRangeSort, ObjectSort), HeapSort, false, false)

  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val nullAddr = new MonoSortedIFunction("null" + addressSortName,
    List(), AddressSort, false, false)

  val valid = new MonoSortedPredicate("valid", List(HeapSort, AddressSort))
  override val isAlloc = valid

  /**
   * Helper function to write to ADT fields.
   * @param lhs : the ADT field term to be written to. This should be an IFunApp,
   *            where the outermost function is a selector of the ADT, the
   *            innermost function is a heap read to the ADT on the heap, the
   *            innermost+1 function is the getter of the ADT, and any
   *            intermediate functions are other selectors
   *            e.g. x(getS(read(h, p))) or  (in C: p->x)
   *                 x(s(getS(read(h, p))))  (in C: p->s.x)
   *            note that this method works for writing to non-ADTs as well,
   *            if lhs is provided as a read Object (e.g. getInt(read(h,p))).
   * @param rhs : the new value for the field, e.g. 42
   * this would return a new term, such as: S(42, y(s))
   * @return    : the new ADT term
   */
  def writeADT (lhs : IFunApp, rhs : ITerm) : ITerm = {
    import IExpression.toFunApplier
    def updateADT(adtStack : List[ADTFieldPath], parentTerm : ITerm,
                  newVal : ITerm) : ITerm = {
      adtStack match {
        case Nil => // last level
          newVal
        case parent :: tl => import IExpression.toFunApplier
          val newTerm = updateADT(tl, parentTerm, newVal)
          val args = for (i <- parent.sels.indices) yield {
            if (i == parent.updatedSelInd) newTerm
            else parent.sels(i)(parentTerm)
          }
          parent.ctor(args : _*)
      }
    }

    val (adtStack, rootTerm) = generateADTUpdateStack(lhs)
    val newTerm = updateADT(adtStack, rootTerm, rhs)
    rootTerm match {
      case IFunApp(f, args) =>
        f match {
          case sortedF: MonoSortedIFunction // Object read (read(h, p))
            if sortedF.resSort == ObjectSort =>
            write(args(0), args(1), newTerm)
          case sortedF: MonoSortedIFunction // getter read (getInt(read(h, p)))
            if userADTSels.exists(s => s contains sortedF) =>
            val readArgs = args.head.asInstanceOf[IFunApp].args
            val wrapper: MonoSortedIFunction =
              userADTCtors.find(f => f.argSorts.size == 1 &&
                f.argSorts.head == Sort.sortOf(rootTerm)) match {
                case None => throw new HeapException(
                  "Could not find a wrapper for " + rootTerm)
                case Some(f) => f
              }
            write(readArgs(0), readArgs(1), wrapper(newTerm))
          case _ => throw new HeapException("Could not determine write from " +
            "the lhs: " + lhs)
        }
      case _ => throw new HeapException("Could not determine write from " +
        "the lhs: " + lhs)
    }
  }

  private case class ADTFieldPath (ctor : MonoSortedIFunction,
                                sels : Seq[MonoSortedIFunction],
                                updatedSelInd : Int)
  private def generateADTUpdateStack (termPointingToADTField : IFunApp)
  : (List[ADTFieldPath], ITerm) = {
    val ADTUpdateStack = new mutable.Stack[ADTFieldPath]

    def fillParentStack (fieldTerm : IFunApp) : ITerm = {
      assert(fieldTerm.args.size == 1 || fieldTerm.fun == read)
      fieldTerm.args.head match {
        case nested : IFunApp if userADTCtors.exists(c =>
          c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort) &&
          nested.fun != read =>

          // here two possibilities:
          // one is that the last level resSort is a getter
          //   (e.g. getS that has the same resSort as a ctor)
          // second is that the last level is simply the ctor
          val ctorInd =
            if(userADTCtors contains nested.fun) { // first case
              userADTCtors indexOf nested.fun
            } else { // second case
              userADTCtors.indexWhere(c =>
                c.resSort == nested.fun.asInstanceOf[MonoSortedIFunction].resSort)
            }

          val sels = userADTSels(ctorInd)
          val thisSelInd =
            userADTSels(ctorInd).indexWhere(s => s == fieldTerm.fun)
          ADTUpdateStack.push(
            ADTFieldPath(userADTCtors(ctorInd), sels, thisSelInd))
          // then move on to nested parents
          fillParentStack(nested)
        case _ => fieldTerm
      }
    }
    val rootTerm = fillParentStack (termPointingToADTField)
    (ADTUpdateStack.toList, rootTerm)
  }

  val counter = new MonoSortedIFunction("counter" + addressSortName,
    List(HeapSort), Sort.Nat, false, false)

  val functions = List(emptyHeap, alloc, allocHeap, allocAddr, read, write,
                       nullAddr, counter, nthAddr, nextAddr, nthAddrRange,
                       batchAlloc, batchAllocHeap, batchAllocAddrRange, nth,
                       batchWrite)
  val predefPredicates = List(isAlloc, within)

  val _defObj : ITerm = defaultObjectCtor(userADTCtors)

  val defaultObject = _defObj

  private def _isAlloc(h: ITerm , p: ITerm) : IFormula = {
    import IExpression._
    counter(h) >= p & p > 0
  }

  val triggeredAxioms : IFormula = {
    import IExpression._
    (
      //row - same (row-upward unit test fails, tested program immediately returns unsat / enters a loop)
      /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
        o => trig(_isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
        read(write(h, p, o), p))))) &*/

      // same as above but simpler trigger, unit tests pass, test program ends with "cannot handle general quantifiers..." error)
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        _isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
          write(h, p, o))))) &

        // row - same (alternative - HeapTests2 - 1.5 does not terminate, row-upward fails)
        //HeapSort.all(h1 => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(
        //  o => trig(_isAlloc(h1, p) & write(h1, p, o) === h2 ==> (read(h2, p) === o),
        //    write(h1, p, o), read(h2, p)))))) &

        // row - same (alternative 2 - unit tests pass, messy interpolants)
        //HeapSort.all(h1 => AddressSort.all(p => ObjectSort.all(
        //  o => trig(_isAlloc(h1, p) ==>
        //    HeapSort.ex(h2 => write(h1, p, o) === h2 & (read(h2, p) === o)),
        //    write(h1, p, o))))) &

        // row - different - downward
        //HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
        //    read(write(h, p1, o), p2)))))) &

        // row - different - downward & upward (some tests fail, including ROW-upward)
        //HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
        //    read(write(h, p1, o), p2), read(h, p2)))))) &

        //
        //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 & write(h, p1, o) === h2 ==> (read(h2, p2) === read(h, p2)),
        //    write(h, p1, o), read(h2, p2))))))) &

        // row - downward
        HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o =>
          AddressSort.all(p2 => trig(
            (p1 =/= p2) ==> (read(write(h, p1, o), p2) === read(h, p2)),
            write(h, p1, o), read(write(h, p1, o), p2)))))) &

        // row - upward
        HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
          p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
            write(h, p1, o), read(h, p2)))))) &

        // same as above, but adding it this way messes everything up, some tests return "inconclusive".
        //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
        //  p2 => trig(p1 =/= p2 & write(h, p1, o) === h2 ==> (read(h2, p2) === read(h, p2)),
        //    write(h, p1, o), read(h, p2))))))) &

        // invalid write - 1
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (counter(h) < p) ==> (write(h, p, o) === h), write(h, p, o))))) &
        // invalid write - 2
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p <= 0) ==> (write(h, p, o) === h), write(h, p, o))))) &

        // invalid bwrite - written heap is unallocated at this address range's start
        HeapSort.all(h => addressRangeSort.all(r => ObjectSort.all(o => trig(
          (counter(h) < addrRangeStart(r)) ==>
            (batchWrite(h, r, o) === h), batchWrite(h, r, o))))) &
        // invalid bwrite 2 - address range starts at nullAddr
        HeapSort.all(h => addressRangeSort.all(r => ObjectSort.all(o => trig(
          (addrRangeStart(r) <= 0) ==>
            (batchWrite(h, r, o) === h), batchWrite(h, r, o))))) &
        // invalid bwrite 3 - address range's end is greater than the size of written heap
        HeapSort.all(h => addressRangeSort.all(r => ObjectSort.all(o => trig(
          ((addrRangeStart(r) + addrRangeSize(r) - 1) > counter(h)) ==>
            (batchWrite(h, r, o) === h), batchWrite(h, r, o))))) &

        // counter is same after write
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          counter(write(h, p, o)) === counter(h), write(h, p, o))))) &

        // counter is same after bwrite
        HeapSort.all(h => addressRangeSort.all(r => ObjectSort.all(o => trig(
          counter(batchWrite(h, r, o)) === counter(h), batchWrite(h, r, o))))) &

        // invalid read - 1
        HeapSort.all(h => AddressSort.all(p => trig(
          (counter(h) < p) ==> containFunctionApplications(read(h, p) === _defObj),
          read(h, p)))) &
        // invalid read - 2
        HeapSort.all(h => AddressSort.all(p => trig(
          (p <= 0) ==> containFunctionApplications(read(h, p) === _defObj),
          read(h, p)))) &

        /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p === counter(h)+1) ==>
          (read(allocHeap(h, o), p) === o ),
            read(allocHeap(h, o), p))))) &

        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p =/= counter(h)+1) ==>
          (read(allocHeap(h, o), p) === read(h, p)),
            read(allocHeap(h, o), p))))))*/
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p === counter(h)+1) ==>
            (read(allocHeap(h, o), p) === o ),
          read(allocHeap(h, o), p), allocHeap(h, o))))) &

        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p =/= counter(h)+1) ==>
            (read(allocHeap(h, o), p) === read(h, p)),
          read(allocHeap(h, o), p), allocHeap(h, o))))) &

        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(n => trig(
          (p > counter(h) & p <= counter(h) + n) ==>
            (read(batchAllocHeap(h, o, n), p) === o) ,
          read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n)))))) &

        // !_within(r, p) split into two axioms
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(n => trig(
          (p <= counter(h)) ==>
            (read(batchAllocHeap(h, o, n), p) === read(h, p)) ,
            read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n)))))) &
        /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(n => trig(
          p > counter(h) + n ==>
            containFunctionApplications(read(batchAllocHeap(h, o, n), p) === _defObj) ,
          read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n))))))*/

        // read over valid batchWrite - 1
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => addressRangeSort.all(r => trig(
          (p >= addrRangeStart(r) & p < addrRangeStart(r) + addrRangeSize(r) &
            ((addrRangeStart(r) + addrRangeSize(r) - 1) <= counter(h))) ==>
            (read(batchWrite(h, r, o), p) === o) ,
          read(batchWrite(h, r, o), p), batchWrite(h, r, o)))))) &

        // read over batchwrite - unmodified locations - 1
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => addressRangeSort.all(r => trig(
          (p < addrRangeStart(r)) ==>
            (read(batchWrite(h, r, o), p) === read(h, p)) ,
          read(batchWrite(h, r, o), p), batchWrite(h, r, o)))))) &
        // read over batchwrite - unmodified locations - 2
        HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => addressRangeSort.all(r => trig(
          (p >= addrRangeStart(r) + addrRangeSize(r)) ==>
            (read(batchWrite(h, r, o), p) === read(h, p)) ,
          read(batchWrite(h, r, o), p), batchWrite(h, r, o)))))) //&
      )
    // roa - downward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p === counter(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === o),
    //      allocHeap(h, o), read(h2, p)))))) &

    // roa - upward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p =/= counter(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === read(h, p)),
    //    allocHeap(h, o), read(h2, p), read(h, p)))))))
  }

  val inductionAxioms : IFormula = {
    import IExpression._
    (
    HeapSort.all(h => trig(counter(h) >= 0, counter(h))) & // todo: why removing this fails some test cases? counter resType is Nat.

    HeapSort.all(h => ObjectSort.all(o => trig(
      counter(allocHeap(h, o)) === counter(h) + 1,
      allocHeap(h, o)))) &

    HeapSort.all(h => ObjectSort.all(o => Sort.Nat.all(n => trig(
      counter(batchAllocHeap(h, o, n)) === counter(h) + n,
      batchAllocHeap(h, o, n)))))
    )
  }

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    otherTheories = List(heapADTs))

  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates
  import IExpression.Predicate
  private val heapFunPredMap = new MHashMap[IFunction, Predicate]
  functionPredicateMapping.map(m => heapFunPredMap.put(m._1, m._2))

  import ap.terfor.TerForConvenience._
  import ap.terfor.conjunctions.Conjunction
  import ap.terfor.preds.Atom
  import ap.terfor.{Formula, TermOrder}
  val axioms2 : Formula = {
    implicit val o : TermOrder = order
    forall(Atom(heapFunPredMap(emptyHeap), List(l(v(0))), order) ==>
           Atom(heapFunPredMap(counter), List(l(v(0)), l(0)), order))
  }

  val axioms = Conjunction.conj(List(axioms1, axioms2), order)

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates : Set[Predicate] = funPredicates.toSet // todo
  /**
   * Information how interpreted predicates should be handled for
   * e-matching.
   */
  import ap.Signature
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map() // todo
  /**
   * A list of functions that should be considered in automatic trigger
   * generation
   */
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  /**
   * Additional axioms that are included if the option
   * <code>+genTotalityAxioms</code> is given to Princess.
   */
  val totalityAxioms : Conjunction = Conjunction.TRUE // todo
  /**
   * Optionally, a plug-in implementing reasoning in this theory
   */
  import ap.proof.goal.Goal
  import ap.proof.theoryPlugins.Plugin
  def plugin: Option[Plugin] = Some(new Plugin {

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
        import goal.facts.arithConj.negativeEqs
        import goal.facts.predConj.positiveLitsWithPred
        val counterLits = positiveLitsWithPred(heapFunPredMap(counter))

        //println(goal.facts + "\n")
        import ap.terfor.TerForConvenience._
        import ap.terfor.linearcombination.{LinearCombination => LC}
        import ap.terfor.Term
        import scala.collection.mutable.ArrayBuffer
        val neqTermArr = /* (neq, (h1, h2, c1, c2)) */
          new ArrayBuffer[(LC, (Term, Term, LC, LC))]
        for (neq <- negativeEqs) {
          val (lhs : Term, rhs : Term) = (neq(0)._2, neq(1)._2)
          val (lhsCounterInd, rhsCounterInd) =
            (counterLits.indexWhere(a => a.head.head._2 == lhs),
             counterLits.indexWhere(a => a.head.head._2 == rhs))

          if(lhsCounterInd >= 0 && rhsCounterInd >= 0){
            //println(Console.GREEN_B + "Both counter literals found for " + lhs + " and " + rhs  + Console.RESET)
            val lhsCounterTerm : LC = counterLits(lhsCounterInd).last
            val rhsCounterTerm : LC = counterLits(rhsCounterInd).last
            neqTermArr += ((neq, (lhs, rhs, lhsCounterTerm, rhsCounterTerm)))
          }
          /*else if (lhsCounterInd + rhsCounterInd > -2) /* at least one found*/
          {
            println(Console.YELLOW_B + "Only one counter literal found for " + lhs + " and " + rhs + Console.RESET)
          } else println(Console.RED_B + "No counter literals found for " + lhs + " nor " + rhs  + Console.RESET)*/
        }

        implicit val to = goal.order
        val (neqsToRemove, neqsToAdd) =
          (for ((neq, (h1, h2, c1, c2)) <- neqTermArr) yield {
            import ap.terfor.TerForConvenience.{l, v}
            val readPred : Predicate = heapFunPredMap(read)
            val neqToAdd : Formula =  disjFor(c1 =/= c2,
                exists(exists(exists(
                c1 >= v(2) & v(2) > 0 & // isAlloc(h1, v(2))
                Atom(readPred, List(l(h1), l(v(2)), l(v(1))), goal.order) &
                Atom(readPred, List(l(h2), l(v(2)), l(v(0))), goal.order) &
                l(v(0)) =/= l(v(1))
              ))))
            (neq, neqToAdd)}).unzip

        if (neqsToRemove.isEmpty) {
          List()
        } else {
          List(
            Plugin.RemoveFacts(
              ap.terfor.equations.NegEquationConj(neqsToRemove, goal.order)),
            Plugin.AddAxiom(List(), conj(neqsToAdd), NativeHeap.this)
          )
        }
      }
    })

  /**
   * Optionally, other theories that this theory depends on.
   */
  override val dependencies : Iterable[Theory] = List(heapADTs)

  lazy val heapRelatedSymbols = {
    val allFuns =
      (functions ++ (for (t <- dependencies; f <- t.functions) yield f)).toSet
    val allPreds =
      (predicates ++ (for (t <- dependencies; p <- t.predicates) yield p)).toSet
    (allFuns, allPreds)
  }

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  override def iPreprocess(f : IFormula,
                           signature : Signature) : (IFormula, Signature) =
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  private def isFunAndMatches (e : IExpression, f : IFunction) : Boolean = {
    e match {
      case IFunApp(`f`, _) => true
      case _ => false
    }
  }
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`isAlloc`, _) if subres(1) == i(0) =>
        //println("Simplified " + t + " to false")
        IBoolLit(false)
      case IAtom(`isAlloc`, _) =>
        //println("Simplified " + t + " to " + _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm]))
        _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm])
      case IFunApp(`nullAddr`, _) =>
        i(0)
      case IFunApp(`nthAddr`, _) =>
        subres.head
      case IFunApp(`nextAddr`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val n    = subres(1).asInstanceOf[ITerm]
        max(List(counter(heap) + n + 1, i(0)))
      }
      case IFunApp(`nthAddrRange`, _) =>
        addressRangeCtor(subres(0).asInstanceOf[ITerm],
                         subres(1).asInstanceOf[ITerm])
      case IFunApp(`write`, _) if subres(1) == i(0) =>
        //println("Simplified " + t + " to " + subres(0))
        subres(0)
      case IFunApp(`write`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        //println("Simplified " + t + " to " + emptyHeap())
        emptyHeap()
      case IFunApp(`read`, _) if subres(1) == i(0) =>
        //println("Simplified " + t + " to " + _defObj)
        _defObj
      case IFunApp(`read`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        //println("Simplified " + t + " to " + _defObj)
        _defObj
      case IFunApp(`counter`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        //println("Simplified " + t + " to " + 0)
        i(0)
      case IFunApp(`newHeap`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, o) = subres(0).asInstanceOf[IFunApp].args
        //println("Simplified " + t + " to " + allocHeap(h, o))
        allocHeap(h, o)
      case IFunApp(`newAddr`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, _) = subres(0).asInstanceOf[IFunApp].args
        //println("Simplified " + t + " to " + counter(h) + 1)
        counter(h) + 1
      case IFunApp(`alloc`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        //println("Simplified " + t + " to " + AllocResADT.constructors.head(allocHeap(h, o), counter(h)+1))
        allocResCtor(allocHeap(h, o), counter(h)+1)
      /*case IFunApp(`allocHeap`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        HeapSort.eps(h2 => h2 === shiftVars(allocHeap(h, o), 1) &
                           counter(h2) === shiftVars(counter(h) + 1, 1))*/
      case IFunApp(`batchAlloc`, _) =>
        val Seq(h, o, n) = subres.take(3).map(_.asInstanceOf[ITerm])
        //        println("Simplified " + t + " to " + BatchAllocResADT.constructors.head(batchAllocHeap(h, o, n),
//          BatchAllocResADT.constructors.head(batchAllocHeap(h, o, n),
//            AddressRangeADT.constructors.head(ite(n > 0, counter(h)+1, counter(h)), n))))
        val addrRangeStartTerm = n match {
          case IIntLit(IdealInt(i)) if i > 0 => counter(h) + 1
          case _ => ite(n > 0, counter(h)+1, counter(h))
        }
        batchAllocResCtor(batchAllocHeap(h, o, n),
          addressRangeCtor(addrRangeStartTerm, n))

      case IFunApp(`newBatchHeap`, _) if isFunAndMatches(subres(0), batchAlloc) =>
        val Seq(h, o, n) = subres(0).asInstanceOf[IFunApp].args
//        println("Simplified " + t + " to " + batchAllocHeap(h, o, n))
        batchAllocHeap(h, o, n)
      case IFunApp(`newAddrRange`, _) if isFunAndMatches(subres(0), batchAlloc) =>
        val Seq(h, _, n) = subres(0).asInstanceOf[IFunApp].args
//        println("Simplified " + t + " to " + batchAllocAddrRange(ite(n > 0, counter(h)+1, counter(h)), n))
        //batchAllocAddrRange(ite(n > 0, counter(h)+1, counter(h)), n)
        val addrRangeStartTerm = n match {
          case IIntLit(IdealInt(i)) if i > 0 => counter(h) + 1
          case _ => ite(n > 0, counter(h)+1, counter(h))
        }
        addressRangeCtor(addrRangeStartTerm, n)

      case IFunApp(`batchAllocAddrRange`, _) =>
        val Seq(h, _, n) = subres.take(3).map(_.asInstanceOf[ITerm])
        addressRangeCtor(ite(n > 0, counter(h)+1, counter(h)), n)

      case IAtom(`within`, _) =>
        val Seq(r, a) = subres.take(2).map(_.asInstanceOf[ITerm])
//        println("Simplified " + t + " to " + _within(r, a))
        a >= addrRangeStart(r) &
          a < addrRangeStart(r) + addrRangeSize(r)

      case IFunApp(`nth`, _) =>
        val Seq(r, n) = subres.take(2).map(_.asInstanceOf[ITerm])
        n match {
          case IIntLit(IdealInt(i)) if i < 0 =>
            0
          case IIntLit(IdealInt(i)) if i >= 0 =>
            ite(n < addrRangeSize(r), addrRangeStart(r) + n, 0)
          case _ =>
            ite(n >= 0 & n < addrRangeSize(r), addrRangeStart(r) + n, 0)
        }
        //addrRangeStart(r) + n

      case IFunApp(`allocAddr`, _) => //allocAddr(h,_) -> counter(h) + 1
        counter(subres(0).asInstanceOf[ITerm]) + 1
      case IFunApp(`deAlloc`, _) =>
        val h1 = subres(0).asInstanceOf[ITerm]
        val newt = HeapSort.eps(h2 => ObjectSort.ex(o =>
          shiftVars(h1, 2) === allocHeap(h2, shiftVars(o,2))))
        //println("Simplified " + t + " to " + newt)
        newt
      case t =>
        /*println(Console.YELLOW_B + t + Console.GREEN_B + " " +
                t.getClass + Console.RESET)
        println(Console.BLUE_B + subres + Console.RESET)*/
        t update subres
    }
  }
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */

  /*override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
    println()
    println("Preprocessing:")
    println(f) //println(Console.YELLOW_B + f.quans + Console.RESET)
    val reducerSettings = Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
      functionalPredicates)
    val after = ReduceWithConjunction(Conjunction.TRUE, order, reducerSettings)(
      f)
    println(" -> " + after)
    println()
    after
  }*/

  /* def preprocess(f : Conjunction, order : TermOrder) : Conjunction = f // todo
  */
  /**
   * Optionally, a plugin for the reducer applied to formulas both before
   * and during proving.
   */
  // val reducerPlugin : ReducerPluginFactory = IdentityReducerPluginFactory // todo
  /**
   * Optionally, a function evaluating theory functions applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalFun(f : IFunApp) : Option[ITerm] = None // todo
  /**
   * Optionally, a function evaluating theory predicates applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalPred(p : IAtom) : Option[Boolean] = None // todo
  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  /* def generateDecoderData(model : Conjunction)
  : Option[Theory.TheoryDecoderData] =
    None */
  // todo
  /**
   * Check whether we can tell that the given combination of theories is
   * sound for checking satisfiability of a problem, i.e., if proof construction
   * ends up in a dead end, can it be concluded that a problem is satisfiable.
   */
  override def isSoundForSat( // todo
                  theories : Seq[Theory],
                  config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  override val postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ Vector(rewriter _)

  //////////////////////////////////////////////////////////////////////////////

  override def printSMTDeclaration : Unit = {
    import SMTLineariser.{asString, quoteIdentifier}

    print("(declare-heap ")
    println(HeapSort.name + " " + AddressSort.name + " " +
          ObjectSort.name)
    println(" " ++ asString(_defObj))
    print(" (")
    print((for(s <- userADTSorts)
      yield ("(" + quoteIdentifier(s.name) + " 0)")) mkString " ")
    println(") (")
    for (num <- userADTSorts.indices) {
      println("  (")
      for ((f, sels) <- userADTCtors zip userADTSels; // todo: should probably be just the object ADT ctors
           if (f.resSort match {
             case s: ADT.ADTProxySort =>
               s.sortNum == num && s.adtTheory == heapADTs
             case _ =>
               false
           })) {
        print(" ")
        ADT.printSMTCtorDeclaration(f, sels)
      }
      println("  )")
    }
    println("))")
  }

  override def SMTDeclarationSideEffects : Seq[Theory] = List(heapADTs)

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this
  Heap register this
  override def toString = "HeapTheory"

  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  def rewriter(expr : IExpression) : IExpression = expr match {
    // add other cases
    case f@IQuantified(EX, subf) =>
      if (f.asInstanceOf[IQuantified].sort == HeapSort) {
        val h1 = ISortedVariable(0, HeapSort)
        subf match {
          case IBinFormula(`And`,
          IEquation(IFunApp(`counter`, Seq(IVariable(0))), n),
          IEquation(IFunApp(`allocHeap`, Seq(IVariable(0), o)), h2)) =>
            val simpf =
              IQuantified(EX, HeapSort, counter(h1) === n &
                h1 === deAlloc(h2) &
                counter(h2) === counter(h1) + 1 &
                read(h2, counter(h2)) === o)
            //println("Simplified: " + f + " to " + simpf)
            simpf
          case _ => expr //println(expr); expr
        }
      }
      else  expr //{println(expr); expr}
    //println("ex:" + expr.asInstanceOf[IQuantified].sort + " " + f); expr
    // simplifies both  forall h: H, !(read(h, _) = o)  and
    //                  forall h: H, read(h, _) = o to false

    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj))
          if !obj.isInstanceOf[IFunApp] => true
        case INot(Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*))))
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj)
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*)))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("simplified: " + f + " to " + "false")
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(_, Seq(IFunApp(`read`, Seq(IVariable(0), _*)), _*)), _)) =>
          true
        case _ =>
          false
      }) => //println("simplified: " + f + " as " + "true")
      IBoolLit(true)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj)
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*)))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("Rewrote: " + f + " as " + "false")
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj))
          if !obj.isInstanceOf[IFunApp] => true
        case INot(Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*))))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) => //println("Rewrote: " + f + " as " + "true")
      IBoolLit(true)
/*
    // todo: probably unnecessary, remove?
    case f@IEquation(left, right) if left == right => // a == a => true
      //println("Rewrote: " + f + " as " + "true")
      IBoolLit(true)

    //todo: probabably unnecessary, remove?
    case f@IEquation(f1, IPlus(IIntLit(IdealInt(-1)), // a == -1 + a + 1 => true
                 IPlus(f2, IIntLit(IdealInt(1))))) if f1 == f2 =>
      //println("Rewrote: " + f + " as " + "true")
      IBoolLit(true)
/*
    // todo: this one is probably unnecessary: rewrites "!ex o. read(_) = o & is-T(o)" as "!is-T(read(_))"
    case eq@ISortedQuantified(ALL, ObjectSort,
      INot(IBinFormula(And,
                       Eq(IFunApp(`read`, readArgs), IVariable(0)),
                       Eq(IFunApp(f, Seq(IVariable(0))), objId)))) if
        ObjectADT.ctorIds.contains(f) =>
      println("Rewrote: " + eq + " as " + (IFunApp(f, Seq(IFunApp(read, readArgs))) =/= objId))
      shiftVars(IFunApp(f, Seq(IFunApp(read, readArgs))) =/= objId, 1, -1)

    // todo: this one is probably unnecessary: rewrites "!ex o. read(_) = o & !is-T(o)" as "is-T(read(_))"
    case eq@ISortedQuantified(ALL, ObjectSort,
      INot(IBinFormula(And,
                       Eq(IFunApp(`read`, readArgs), IVariable(0)),
                       INot(Eq(IFunApp(f, Seq(IVariable(0))), objId))))) if
        ObjectADT.ctorIds.contains(f) =>
      println("Rewrote: " + eq + " as " + (IFunApp(f, Seq(IFunApp(read, readArgs))) === objId))
      shiftVars(IFunApp(f, Seq(IFunApp(read, readArgs))) === objId, 1, -1))*/

    // ALL HeapObject. !(!(_0[HeapObject] = o1) & (o2 = _0[HeapObject]))
    /*case eq@ISortedQuantified(ALL, ObjectSort,
      INot(IBinFormula(And,
                       INot(Eq(IVariable(0), o1)),
                       Eq(o2, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(o1 === o2, 1, -1))
      shiftVars(o1 === o2, 1, -1)*/

    case eq@IQuantified(ALL,
      INot(IBinFormula(And,
                       Eq(IVariable(0), v1),
                       Eq(v2, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(v1 =/= v2, 1, -1))
      shiftVars(v1 =/= v2, 1, -1)
    case eq@IQuantified(ALL,
      INot(IBinFormula(And,
                       Eq(v1, IVariable(0)),
                       Eq(v2, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(v1 =/= v2, 1, -1))
      shiftVars(v1 =/= v2, 1, -1)
    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(v1, IVariable(0)),
    Eq(IVariable(0), v2)))) =>
      println("Rewrote: " + eq + " as " + shiftVars(v1 =/= v2, 1, -1))
      shiftVars(v1 =/= v2, 1, -1)
    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(IVariable(0), v1),
    Eq(IVariable(0), v2)))) =>
      println("Rewrote: " + eq + " as " + shiftVars(v1 =/= v2, 1, -1))
      shiftVars(v1 =/= v2, 1, -1)

    // ALL x. ! ((v1 = x) & !(f(x) = v2)) --> f(v1) = v2
    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(v1, IVariable(0)),
    INot(Eq(IFunApp(f, Seq(IVariable(0))), v2))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(IFunApp(f, Seq(v1)) === v2, 1, -1))
      shiftVars(IFunApp(f, Seq(v1)) === v2, 1, -1)

    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(v1, IVariable(0)),
    Eq(IFunApp(f, Seq(IVariable(0))), v2)))) =>
      println("Rewrote: " + eq + " as " + shiftVars(IFunApp(f, Seq(v1)) =/= v2, 1, -1))
      shiftVars(IFunApp(f, Seq(v1)) =/= v2, 1, -1)

    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(IFunApp(`read`, Seq(h, IVariable(0))), v1),
    Eq(v2, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(IFunApp(read, Seq(h, v2)) =/= v1, 1, -1))
      shiftVars(IFunApp(read, Seq(h, v2)) =/= v1, 1, -1)

    case eq@IQuantified(ALL,
    INot(IBinFormula(And,
    Eq(IFunApp(f, Seq(IVariable(0))), v2),
    Eq(v1, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(IFunApp(f, Seq(v1)) =/= v2, 1, -1))
      shiftVars(IFunApp(f, Seq(v1)) =/= v2, 1, -1)

    // ALL HeapObject. !ALL HeapObject. !(!(_0[HeapObject] = _1[HeapObject]) & (defObj = _0[HeapObject]))
    case eq@ISortedQuantified(ALL, ObjectSort,
      INot(ISortedQuantified(ALL, ObjectSort,
        INot(IBinFormula(And, INot(IEquation(IVariable(0), IVariable(1))), IEquation(o, IVariable(0))))))) =>
      println("Rewrote: " + eq + " as false")
      false

    // ALL !(((_0 + -1) >= 0) & (next(_1[node]) = _0))
    case eq@IQuantified(ALL, INot(IBinFormula(And, GeqZ(IPlus(IVariable(0), plusVal)), Eq(v, IVariable(0))))) =>
      println("Rewrote: " + eq + " as " + shiftVars(INot(GeqZ(IPlus(v, plusVal))), 1, -1))
      shiftVars(INot(GeqZ(IPlus(v, plusVal))), 1, -1)

    /*
      ALL HeapObject.!((v1 = _0[HeapObject]) & !ALL node. !((next(_0[node]) = v2) &(getnode(_1[HeapObject]) = _0[node])))
        to
      next(getnode(v1)) =/= v2
   */
    case eq@IQuantified(ALL, INot(IBinFormula(And,
    Eq(v1, IVariable(0)),
    INot(IQuantified(ALL, INot(IBinFormula(And, Eq(IFunApp(f1, Seq(IVariable(0))), v2), Eq(IFunApp(f2, Seq(IVariable(1))), IVariable(0))))))
    ))) =>
      println("Rewrote: " + eq + " as " + shiftVars(IFunApp(f1,Seq(IFunApp(f2, Seq(v1)))) =/= v2, 2, -2))
      shiftVars(IFunApp(f1,Seq(IFunApp(f2, Seq(v1)))) =/= v2, 2, -2)

    case eq@IQuantified(_, subf) =>
      println("unhandled: " + eq)
      eq
*/
    /*case IQuantified(ALL, f) =>
      println(expr); expr*/
    /*case Eq(IFunApp(`counter`, Seq(h)), IIntLit(IdealInt(0))) =>
      println("Simplified: " + expr + " to " + (h === emptyHeap()))
      h === emptyHeap()*/
    /*case IFunApp(`read`, Seq(_, IIntLit(IdealInt(0)))) =>
      println("Rewrote: " + expr + " to " + _defObj)
      _defObj*/
    /*case Eq(`_defObj`, IFunApp(`read`, Seq(h, p))) =>
      println("Simplified: " + expr + " to " + !_isAlloc(h, p))
      !_isAlloc(h, p) */
    case _ => expr
  }

}
