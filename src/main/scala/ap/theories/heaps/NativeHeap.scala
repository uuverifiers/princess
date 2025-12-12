/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2025 Philipp Ruemmer <ph_r@gmx.net>
 *               2020-2025 Zafer Esen <zafer.esen@gmail.com>
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
import ap.parser._
import ap.types._
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, Map => MMap,
                                 Set => MSet}
import scala.collection.{mutable, Map => GMap}

object NativeHeap {
  private val AC = Debug.AC_HEAP
  
  class HeapException(m : String) extends Exception(m)
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
class NativeHeap(heapSortName      : String, addressSortName : String,
                 rangeSortName     : String,
                 objectSort        : Heap.ADTSort,
                 sortNames         : Seq[String],
                 ctorSignatures    : Seq[(String, Heap.CtorSignature)],
                 defaultObjectCtor : Seq[MonoSortedIFunction] => ITerm)
  extends Heap {

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

  object AddressSort extends ProxySort(Sort.Nat) with Theory.TheorySort {
    import IExpression.toFunApplier

    override val name = addressSortName
    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      d.intValue match {
        case 0 => Some(nullAddr())
        case v => Some(addr(v))
      }
    }

    override val individuals : LazyList[ITerm] =
      for (t <- Sort.Nat.individuals) yield addr(t)

    val theory = NativeHeap.this
  }

  object HeapSort extends ProxySort(Sort.Integer) with Theory.TheorySort {
    import IExpression.toFunApplier
    import ap.terfor.conjunctions.Conjunction
    import ap.terfor.preds.Atom
    override val name = heapSortName

    val theory = NativeHeap.this

    override val individuals : LazyList[ITerm] =
      emptyHeap() #:: (for (t <- individuals;
                            obj <- ObjectSort.individuals)
      yield heapAddrPair_1(alloc(t, obj)))

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
        model.predConj positiveLitsWithPred heapFunPredMap(f)
      def getHeapADTAtoms (f : IFunction) : IndexedSeq[Atom] =
        model.predConj positiveLitsWithPred heapADTs.
          functionPredicateMapping.find(_._1 == f).get._2

      /* Collect the relevant functions and predicates of the theory */
      val writeAtoms = getAtoms(write)
      val allocAtoms = getAtoms(allocHeap)
      val allocRangeAtoms = getAtoms(batchAllocHeap)
      val writeRangeAtoms = getAtoms(writeRange)
      val rangeStartAtoms = getHeapADTAtoms(rangeStart)
      val rangeSizeAtoms = getHeapADTAtoms(rangeSize)
      val readAtoms = getAtoms(read)
      val heapSizeAtoms = getAtoms(heapSize)
      val emptyHeapAtoms = getAtoms(emptyHeap)

      import IExpression.{i, toFunApplier}

      // Turns a sequence of heap contents into a formula using
      // emptyHeap, alloc and allocRange. Consecutive elements are compressed
      // using allocRange.
      def createHeapTerm(contents : Seq[IdealInt]) : ITerm = {
        // Input: [A, A, B, A] -> Output: List((A, 2), (B, 1), (A, 1))
        def runLengthEncode[T](seq : Seq[T]) : List[(T, Int)] = {
          seq.foldRight(List.empty[(T, Int)]) {
            case (e, (hVal, hCount) :: tail) if e == hVal =>
              (hVal, hCount + 1) :: tail
            case (e, acc) =>
              (e, 1) :: acc
          }
        }

        val compressedContents = runLengthEncode(contents)

        compressedContents.foldLeft(emptyHeap() : ITerm) {
          case (currentHeap, (objId, count)) =>
            val objTerm = terms.getOrElse((objId, ObjectSort), defaultObject)
            if (count > 1)
              heapRangePair_1(allocRange(currentHeap, objTerm, count))
            else
              heapAddrPair_1(alloc(currentHeap, objTerm))
        }
      }

      val heapContents = new MHashMap[IdealInt, ArrayBuffer[IdealInt]] //[eh->[],h1:[1,2],...]

      // fill in the contents for empty heaps
      for (a <- emptyHeapAtoms) { // emptyHeap(heapId)
        heapContents += ((a(0).constant, new ArrayBuffer[IdealInt](0)))
      }

      // Map[range(rangeId -> (addRangeStartId : IdealInt,
      //                               rangeSize : Int))]
      val rangeInfo =
        (for (rangeSizePair <- (rangeStartAtoms.sortBy(_(0).constant.intValue) zip
                                    rangeSizeAtoms.sortBy(_(0).constant.intValue))) yield {
          val rangeId = rangeSizePair._1(0).constant
          assert (rangeId == rangeSizePair._2(0).constant)
          (rangeId, (rangeSizePair._1(1).constant,
            rangeSizePair._2(1).constant.intValue))
        }).toMap

      // initialize content buffers of non-empty heaps
      // heapSize(heapId, heapSizeVal)
      for (a <- heapSizeAtoms) {
        val heapId = a(0).constant
        val heapSizeVal = a(1).constant
        val contentBuffer = new ArrayBuffer[IdealInt](heapSizeVal.intValue)
        for (_ <- 0 until heapSizeVal.intValue)
          contentBuffer += -1
        heapContents += ((heapId,contentBuffer))
      }

      var somethingChanged = true
      // iterate over non-empty heaps to fixed-point
      while(somethingChanged) {
        somethingChanged = false
        for (a <- heapSizeAtoms) {
          val heapId = a(0).constant
          val heapSizeVal = a(1).constant
          /*
        * A heap is either created through an alloc(Range), or through a write.
        * If it is created through alloc, all locations except the last location
        * (i.e., heapSizeVal), are the same as the original heap.
        * If it is craeted through allocRange, all locations except the last n
        * locations are the same as the original heap, where n is the batch size.
        * If it is created through write, all locations except the written
        * location, are the same as the original heap.
        */

          // batchAllocHeap(prevHeapId, obj, n, heapId)
          val (prevHeapId, changedAddr, newObj, allocOrWriteFound, changeSize) =
            allocRangeAtoms.find(p => p(3).constant == heapId) match {
              case Some(p) =>
                val n = p(2).constant.intValue
                (p(0).constant, heapSizeVal, p(1).constant, true,
                  if (n > 0) n else 0)
              case None =>
                // allocHeap(prevHeapId, obj, heapId)
                allocAtoms.find(p => p(2).constant == heapId) match {
                  case Some(p) =>
                    (p(0).constant, heapSizeVal, p(1).constant, true, 1)
                  case None => // no allocs found, then there must be a write
                    // write(prevHeapId, addr, obj, heapId)
                    writeAtoms.find(p => p(3).constant == heapId) match {
                      case Some(p) =>
                        (p(0).constant, p(1).constant, p(2).constant, true, 1)
                      case None =>
                        // batchWrite(prevHeapId, range, obj, heapId)
                        writeRangeAtoms find (p =>
                          p(3).constant == heapId) match {
                          case Some (p) =>
                            val (rangeStart, rangeSize) =
                              rangeInfo.getOrElse(p(1).constant, (IdealInt(-1), 0))
                            (p(0).constant, // prevHeapID
                              rangeStart + rangeSize - 1, // last changed address
                              p(2).constant, // object
                              rangeStart != IdealInt(-1), // false if addrStart could not be determined
                              rangeSize) // size of change
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
      for (a <- heapSizeAtoms) {
        val heapId = a(0).constant
        val heapKey = (heapId, this)

        // if one of the object terms has not been yet defined, return
        for (id <- heapContents(heapId))
          if ((allTerms exists (key => key._1 == id)) &&
              !(terms exists (term => term._1._1 == id)))
            return

        val heapTerm = createHeapTerm(heapContents(heapId).toSeq)
        if (!(definedTerms contains heapKey) || //if this term is not defined
            (terms(heapKey) != heapTerm)) { // or has changed
          terms.put(heapKey, heapTerm) //update the heap term
          if (!(definedTerms contains heapKey)) definedTerms += heapKey
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////
  val emptyHeap = new MonoSortedIFunction(Heap.Names.Empty,
                                          argSorts = List(),
                                          resSort = HeapSort,
                                          _partial = false, _relational = false)

  val addr = new MonoSortedIFunction(Heap.Names.Addr,
                                     List(Sort.Nat), AddressSort,
                                     false, false)
  val nextAddr =
    new MonoSortedIFunction(Heap.Names.NextAddr,
                            List(HeapSort, Sort.Integer), AddressSort,
                            false, false)

  object HeapADTSortId extends Enumeration(initial = sortNames.size) {
    type HeapADTSortId = Value
    val heapAddrPairSortId, heapRangePairSortId, rangeSortId = Value
  }
  import HeapADTSortId._

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort   => ADT.ADTSort(t.num)
      case t : OtherSort => ADT.OtherSort(t.sort)
      case AddrSort      => ADT.OtherSort(AddressSort)
      case AddrRangeSort => ADT.ADTSort(rangeSortId)
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
  private val heapAddrPairCtorSignature = ADT.CtorSignature(
    List((Heap.Names.HeapAddrPair_1, ADT.OtherSort(HeapSort)),
         (Heap.Names.HeapAddrPair_2, ADT.OtherSort(AddressSort))),
    ADT.ADTSort(heapAddrPairSortId))

  /** Create range ADT returned by batchAlloc: start x size */
  private val rangeCtorSignature = ADT.CtorSignature(
    List(("heap.rangeStart", ADT.OtherSort(AddressSort)),
         (Heap.Names.RangeSize, ADT.OtherSort(Sort.Nat))),
    ADT.ADTSort(rangeSortId))
  /** Create return sort of batchAlloc as an ADT: Heap x Range */
  private val heapRangePairCtorSignature = ADT.CtorSignature(
    List((Heap.Names.HeapRangePair_1, ADT.OtherSort(HeapSort)),
         (Heap.Names.HeapRangePair_2, ADT.ADTSort(rangeSortId))),
    ADT.ADTSort(heapRangePairSortId))

  // warning: heap ADTs must be declared last!
  // Also if any new heap ADT is added here, the sort extractor must be
  //   extended!
  val heapADTDefinitions : Map[HeapADTSortId, (String, ADT.CtorSignature)] = Map(
    (heapAddrPairSortId, (Heap.Names.Pair(heapSortName, addressSortName),
      heapAddrPairCtorSignature)),
    (heapRangePairSortId, (Heap.Names.Pair(heapSortName, rangeSortName),
      heapRangePairCtorSignature)),
    (rangeSortId, (rangeSortName, rangeCtorSignature))
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

  val HeapAddressPairSort = theoryADTSorts(heapAddrPairSortId - sortNames.size)
  private val heapAddressPairCtor =
    theoryADTCtors(heapAddrPairSortId - sortNames.size)
  val heapAddrPair_1 = theoryADTSels(heapAddrPairSortId - sortNames.size)(0)
  val heapAddrPair_2 = theoryADTSels(heapAddrPairSortId - sortNames.size)(1)

  val HeapRangePairSort = theoryADTSorts(heapRangePairSortId - sortNames.size)
  private val heapRangePairCtor =
    theoryADTCtors(heapRangePairSortId - sortNames.size)
  val heapRangePair_1 = theoryADTSels(heapRangePairSortId - sortNames.size)(0)
  val heapRangePair_2 = theoryADTSels(heapRangePairSortId - sortNames.size)(1)

  val RangeSort   = theoryADTSorts(rangeSortId-sortNames.size)
  private val rangeCtor   = theoryADTCtors(rangeSortId-sortNames.size)
  private val rangeStart  = theoryADTSels(rangeSortId-sortNames.size)(0)
  val rangeSize   = theoryADTSels(rangeSortId - sortNames.size)(1)

  val range =
    new MonoSortedIFunction(Heap.Names.Range, List(Sort.Nat, Sort.Nat),
                            RangeSort, false, false)

  val rangeNth =
    new MonoSortedIFunction(Heap.Names.RangeNth,
                            List(RangeSort, Sort.Nat), AddressSort,
                            false, false)
  val rangeWithin =
    new MonoSortedPredicate(Heap.Names.RangeWithin,
                            List(RangeSort, AddressSort))

  /** See the [[Heap]] trait for functions and predicates of the theory
   * writeADT : Obj x Obj --> Heap
   * * Updates the ADT's field (described by a read to 0) using value (1)
   * ***************************************************************************
   * Private functions and predicates
   * ***************************************************************************
   * heapSize        : Heap --> Nat
   *
   * * Below two functions are shorthand functions to get rid of HeapAddrPair.
   * * They return a single value instead of the pair <Heap x Addr>.
   * * This also removes some quantifiers related to the ADT in the generated
   * * interpolants.
   * allocHeap       : Heap x Obj --> Heap
   * allocAddr       : Heap x Obj --> Address
   *
   * * Below two functions are shorthand functions to get rid of HeapRangePair.
   * * They return a single value instead of the pair <Heap x Range>.
   * * This also removes some quantifiers related to the ADT in the generated
   * * interpolants.
   * batchAllocHeap  : Heap x Obj x Nat --> Heap
   * batchAllocRange : Heap x Obj x Nat --> Range
   * *
   * ***************************************************************************
   * */
  val alloc =
    new MonoSortedIFunction(Heap.Names.Alloc, List(HeapSort, ObjectSort),
                            HeapAddressPairSort, false, false)
  private val allocHeap =
    new MonoSortedIFunction("allocHeap",
                            List(HeapSort, ObjectSort), HeapSort, false, false)
  private val allocAddr =
    new MonoSortedIFunction("allocAddr",
                            List(HeapSort, ObjectSort), AddressSort,
                            false, false)
  private val deAlloc =
    new MonoSortedIFunction("deAlloc", List(HeapSort), HeapSort, false, false)

  val allocRange =
    new MonoSortedIFunction(Heap.Names.AllocRange,
                            List(HeapSort, ObjectSort, Sort.Nat),
                            HeapRangePairSort, false, false)
  private val batchAllocHeap =
    new MonoSortedIFunction("rangeAllocHeap",
                            List(HeapSort, ObjectSort, Sort.Nat), HeapSort,
                            false, false)
  private val batchAllocRange =
    new MonoSortedIFunction("rangeAllocAddr",
                            List(HeapSort, ObjectSort, Sort.Nat),
                            RangeSort, false, false)
  val writeRange =
    new MonoSortedIFunction(Heap.Names.WriteRange,
                            List(HeapSort, RangeSort, ObjectSort),
                            HeapSort, false, false)

  val read =
    new MonoSortedIFunction(Heap.Names.Read, List(HeapSort, AddressSort),
                            ObjectSort, false, false)
  val write =
    new MonoSortedIFunction(Heap.Names.Write,
                            List(HeapSort, AddressSort, ObjectSort),
                            HeapSort, false, false)
  val nullAddr =
    new MonoSortedIFunction(Heap.Names.Null, List(), AddressSort, false, false)

  val valid =
    new MonoSortedPredicate(Heap.Names.Valid, List(HeapSort, AddressSort))

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

  val heapSize =
    new MonoSortedIFunction("heap.size", List(HeapSort), Sort.Nat,
                            false, false)

  val functions = List(emptyHeap, alloc, allocHeap, allocAddr, read, write,
                       nullAddr, heapSize, addr, nextAddr, range,
                       allocRange, batchAllocHeap, batchAllocRange,
                       rangeNth, writeRange)
  val predefPredicates = List(valid, rangeWithin)

  val defaultObject : ITerm = defaultObjectCtor(userADTCtors)

  private def _isAlloc(h: ITerm , p: ITerm) : IFormula = {
    import IExpression._
    heapSize(h) >= p & p > 0
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
        (heapSize(h) < p) ==> (write(h, p, o) === h), write(h, p, o))))) &
      // invalid write - 2
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
          (p <= 0) ==> (write(h, p, o) === h), write(h, p, o))))) &

      // invalid bwrite - written heap is unallocated at this address range's start
      HeapSort.all(h => RangeSort.all(r => ObjectSort.all(o => trig(
        (heapSize(h) < rangeStart(r)) ==>
        (writeRange(h, r, o) === h), writeRange(h, r, o))))) &
      // invalid bwrite 2 - address range starts at nullAddr
      HeapSort.all(h => RangeSort.all(r => ObjectSort.all(o => trig(
          (rangeStart(r) <= 0) ==>
            (writeRange(h, r, o) === h), writeRange(h, r, o))))) &
      // invalid bwrite 3 - address range's end is greater than the size of written heap
      HeapSort.all(h => RangeSort.all(r => ObjectSort.all(o => trig(
        ((rangeStart(r) + rangeSize(r) - 1) > heapSize(h)) ==>
        (writeRange(h, r, o) === h), writeRange(h, r, o))))) &

      // heapSize is same after write
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        heapSize(write(h, p, o)) === heapSize(h), write(h, p, o))))) &

      // heapSize is same after bwrite
      HeapSort.all(h => RangeSort.all(r => ObjectSort.all(o => trig(
        heapSize(writeRange(h, r, o)) === heapSize(h), writeRange(h, r, o))))) &

      // invalid read - 1
      HeapSort.all(h => AddressSort.all(p => trig(
        (heapSize(h) < p) ==> containFunctionApplications(read(h, p) === defaultObject),
        read(h, p)))) &
      // invalid read - 2
      HeapSort.all(h => AddressSort.all(p => trig(
          (p <= 0) ==> containFunctionApplications(read(h, p) === defaultObject),
          read(h, p)))) &

      /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        (p === heapSize(h)+1) ==>
        (read(allocHeap(h, o), p) === o ),
          read(allocHeap(h, o), p))))) &

      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        (p =/= heapSize(h)+1) ==>
        (read(allocHeap(h, o), p) === read(h, p)),
          read(allocHeap(h, o), p))))))*/
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        (p === heapSize(h) + 1) ==>
        (read(allocHeap(h, o), p) === o ),
          read(allocHeap(h, o), p), allocHeap(h, o))))) &

      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
        (p =/= heapSize(h) + 1) ==>
        (read(allocHeap(h, o), p) === read(h, p)),
          read(allocHeap(h, o), p), allocHeap(h, o))))) &

      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(
          n => trig(
            (p > heapSize(h) & p <= heapSize(h) + n) ==>
            (read(batchAllocHeap(h, o, n), p) === o) ,
          read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n)))))) &

      // !_within(r, p) split into two axioms
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(
          n => trig(
            (p <= heapSize(h)) ==>
            (read(batchAllocHeap(h, o, n), p) === read(h, p)) ,
            read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n)))))) &
      /*HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => Sort.Nat.all(n => trig(
        p > heapSize(h) + n ==>
          containFunctionApplications(read(batchAllocHeap(h, o, n), p) === defaultObject) ,
        read(batchAllocHeap(h, o, n), p), batchAllocHeap(h, o, n))))))*/

      // read over valid batchWrite - 1
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => RangeSort.all(r => trig(
            (p >= rangeStart(r) & p < rangeStart(r) + rangeSize(r) &
            ((rangeStart(r) + rangeSize(r) - 1) <= heapSize(h))) ==>
            (read(writeRange(h, r, o), p) === o),
            read(writeRange(h, r, o), p), writeRange(h, r, o)))))) &

      // read over batchwrite - unmodified locations - 1
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => RangeSort.all(r => trig(
          (p < rangeStart(r)) ==>
            (read(writeRange(h, r, o), p) === read(h, p)),
          read(writeRange(h, r, o), p), writeRange(h, r, o)))))) &
      // read over batchwrite - unmodified locations - 2
      HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
          o => RangeSort.all(r => trig(
          (p >= rangeStart(r) + rangeSize(r)) ==>
            (read(writeRange(h, r, o), p) === read(h, p)),
          read(writeRange(h, r, o), p), writeRange(h, r, o)))))) //&
      )
    // roa - downward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p === heapSize(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === o),
    //      allocHeap(h, o), read(h2, p)))))) &

    // roa - upward
    //HeapSort.all(h => HeapSort.all(h2 => AddressSort.all(p => ObjectSort.all(o => trig(
    //    (p =/= heapSize(h)+1 & allocHeap(h, o) === h2) ==>
    //      (read(h2, p) === read(h, p)),
    //    allocHeap(h, o), read(h2, p), read(h, p)))))))
  }

  val inductionAxioms : IFormula = {
    import IExpression._
    (
      HeapSort.all(h => trig(heapSize(h) >= 0, heapSize(h))) & // todo: why removing this fails some test cases? heapSize resType is Nat.

      HeapSort.all(h => ObjectSort.all(o => trig(
        heapSize(allocHeap(h, o)) === heapSize(h) + 1,
        allocHeap(h, o)))) &

      HeapSort.all(h => ObjectSort.all(o => Sort.Nat.all(n => trig(
        heapSize(batchAllocHeap(h, o, n)) === heapSize(h) + n,
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
           Atom(heapFunPredMap(heapSize), List(l(v(0)), l(0)), order))
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
        val heapSizeLits = positiveLitsWithPred(heapFunPredMap(heapSize))

        import ap.terfor.TerForConvenience._
        import ap.terfor.linearcombination.{LinearCombination => LC}
        import ap.terfor.Term
        import scala.collection.mutable.ArrayBuffer
        val neqTermArr = /* (neq, (h1, h2, c1, c2)) */
          new ArrayBuffer[(LC, (Term, Term, LC, LC))]
        for (neq <- negativeEqs) {
          val (lhs : Term, rhs : Term) = (neq(0)._2, neq(1)._2)
          val (lhsHeapSizeInd, rhsHeapSizeInd) =
            (heapSizeLits.indexWhere(a => a.head.head._2 == lhs),
             heapSizeLits.indexWhere(a => a.head.head._2 == rhs))

          if(lhsHeapSizeInd >= 0 && rhsHeapSizeInd >= 0){
            val lhsHeapSizeTerm : LC = heapSizeLits(lhsHeapSizeInd).last
            val rhsHeapSizeTerm : LC = heapSizeLits(rhsHeapSizeInd).last
            neqTermArr += ((neq, (lhs, rhs, lhsHeapSizeTerm, rhsHeapSizeTerm)))
          }
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
      case IAtom(`valid`, _) if subres(1) == i(0) =>
        IBoolLit(false)
      case IAtom(`valid`, _) =>
        _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm])
      case IFunApp(`nullAddr`, _) =>
        i(0)
      case IFunApp(`addr`, _) =>
        subres.head
      case IFunApp(`nextAddr`, _) => {
        val heap = subres(0).asInstanceOf[ITerm]
        val n    = subres(1).asInstanceOf[ITerm]
        max(List(heapSize(heap) + n + 1, i(0)))
      }
      case IFunApp(`range`, _) =>
        rangeCtor(subres(0).asInstanceOf[ITerm],
                         subres(1).asInstanceOf[ITerm])
      case IFunApp(`write`, _) if subres(1) == i(0) =>
        subres(0)
      case IFunApp(`write`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        emptyHeap()
      case IFunApp(`read`, _) if subres(1) == i(0) =>
        defaultObject
      case IFunApp(`read`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        defaultObject
      case IFunApp(`heapSize`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        i(0)
      case IFunApp(`heapAddrPair_1`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, o) = subres(0).asInstanceOf[IFunApp].args
        allocHeap(h, o)
      case IFunApp(`heapAddrPair_2`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, _) = subres(0).asInstanceOf[IFunApp].args
        heapSize(h) + 1
      case IFunApp(`alloc`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        heapAddressPairCtor(allocHeap(h, o), heapSize(h) + 1)
      case IFunApp(`allocRange`, _) =>
        val Seq(h, o, n) = subres.take(3).map(_.asInstanceOf[ITerm])
        val rangeStartTerm = n match {
          case IIntLit(IdealInt(i)) if i > 0 => heapSize(h) + 1
          case _ => ite(n > 0, heapSize(h) + 1, heapSize(h))
        }
        heapRangePairCtor(batchAllocHeap(h, o, n),
                          rangeCtor(rangeStartTerm, n))

      case IFunApp(`heapRangePair_1`, _)
        if isFunAndMatches(subres(0), allocRange) =>
        val Seq(h, o, n) = subres(0).asInstanceOf[IFunApp].args
        batchAllocHeap(h, o, n)
      case IFunApp(`heapRangePair_2`, _)
        if isFunAndMatches(subres(0), allocRange) =>
        val Seq(h, _, n) = subres(0).asInstanceOf[IFunApp].args
        val rangeStartTerm = n match {
          case IIntLit(IdealInt(i)) if i > 0 => heapSize(h) + 1
          case _ => ite(n > 0, heapSize(h) + 1, heapSize(h))
        }
        rangeCtor(rangeStartTerm, n)

      case IFunApp(`batchAllocRange`, _) =>
        val Seq(h, _, n) = subres.take(3).map(_.asInstanceOf[ITerm])
        rangeCtor(ite(n > 0, heapSize(h) + 1, heapSize(h)), n)

      case IAtom(`rangeWithin`, _) =>
        val Seq(r, a) = subres.take(2).map(_.asInstanceOf[ITerm])
        a >= rangeStart(r) &
          a < rangeStart(r) + rangeSize(r)

      case IFunApp(`rangeNth`, _) =>
        val Seq(r, n) = subres.take(2).map(_.asInstanceOf[ITerm])
        n match {
          case IIntLit(IdealInt(i)) if i < 0 =>
            0
          case IIntLit(IdealInt(i)) if i >= 0 =>
            ite(n < rangeSize(r), rangeStart(r) + n, 0)
          case _ =>
            ite(n >= 0 & n < rangeSize(r), rangeStart(r) + n, 0)
        }

      case IFunApp(`allocAddr`, _) =>
        heapSize(subres(0).asInstanceOf[ITerm]) + 1
      case IFunApp(`deAlloc`, _) =>
        val h1 = subres(0).asInstanceOf[ITerm]
        val newt = HeapSort.eps(h2 => ObjectSort.ex(o =>
          shiftVars(h1, 2) === allocHeap(h2, shiftVars(o,2))))
        newt
      case t =>
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

  TheoryRegistry register this
  Heap register this
  override def toString = "HeapTheory"

  import IBinJunctor._
  import IExpression._
  import Quantifier._

  def rewriter(expr : IExpression) : IExpression = expr match {
    // add other cases
    case f@IQuantified(EX, subf) =>
      if (f.sort == HeapSort) {
        val h1 = ISortedVariable(0, HeapSort)
        subf match {
          case IBinFormula(`And`,
          IEquation(IFunApp(`heapSize`, Seq(IVariable(0))), n),
          IEquation(IFunApp(`allocHeap`, Seq(IVariable(0), o)), h2)) =>
            val simpf =
              IQuantified(EX, HeapSort,
                          heapSize(h1) === n &
                          h1 === deAlloc(h2) &
                          heapSize(h2) === heapSize(h1) + 1 &
                          read(h2, heapSize(h2)) === o)
            simpf
          case _ => expr
        }
      }
      else  expr

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
      }) =>
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(_, Seq(IFunApp(`read`, Seq(IVariable(0), _*)), _*)), _)) =>
          true
        case _ =>
          false
      }) =>
      IBoolLit(true)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj)
          if !obj.isInstanceOf[IFunApp] => true
        case Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*)))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) =>
      IBoolLit(false)
    case f@IQuantified(ALL, subf) if f.sort == HeapSort &
      (subf match {
        case INot(Eq(IFunApp(`read`, Seq(IVariable(0), _*)), obj))
          if !obj.isInstanceOf[IFunApp] => true
        case INot(Eq(obj, IFunApp(`read`, Seq(IVariable(0), _*))))
          if !obj.isInstanceOf[IFunApp] => true
        case _  => false
      }) =>
      IBoolLit(true)
    case _ => expr
  }

}
