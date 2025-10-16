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

import ap.types.{Sort, MonoSortedIFunction}
import ap.theories.Theory
import ap.parser.{IFunction, ITerm, IFormula, IExpression}
import IExpression.Predicate

import scala.collection.mutable.{HashMap => MHashMap}

/**
 * Companion object for the trait implemented by the different heap theories.
 */
object Heap {

  /**
   * Abstract class for the sorts that the heap ADT can refer to.
   */
  abstract sealed class CtorArgSort

  /**
   * Reference to the num'th heap ADT sort.
   */
  case class ADTSort(num : Int)       extends CtorArgSort

  /**
   * Reference to some externally defined sort.
   */
  case class OtherSort(sort : Sort)   extends CtorArgSort

  /**
   * Reference to the address sort that is specific to the heap to be declared.
   */
  case object AddrSort                extends CtorArgSort

  /**
   * Reference to the address range sort that is specific to the heap to be
   * declared.
   */
  case object AddrRangeSort           extends CtorArgSort

  /**
   * Specification of a heap ADT constructor.
   */
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  // General convention is that addressRange sort name is
  // addressName + addressRangeSuffix
  val AddressRangeSuffix = "Range"

  /**
   * Extractor to recognise any sort related to a heap theory.
   * This includes the sorts for heaps and addresses, address ranges,
   * user defined ADT sorts, etc.
   */
  object HeapRelatedSort {
    def unapply(s : Sort) : Option[Heap] = synchronized { heapSorts get s }
  }

  private val heapSorts = new MHashMap[Sort, Heap]

  def register(t : Heap) : Unit = synchronized {
    heapSorts.put(t.HeapSort,          t)
    heapSorts.put(t.AddressSort,       t)
    heapSorts.put(t.AddressRangeSort,  t)
    heapSorts.put(t.AllocResSort,      t)
    heapSorts.put(t.BatchAllocResSort, t)

    for (s <- t.userHeapSorts)
      heapSorts.put(s, t)
  }

}

/**
 * Trait implemented by the different heap theories.
 */
trait Heap extends Theory {

  /**
   * Sort of heaps in this heap theory.
   */
  val HeapSort : Sort

  /**
   * Sort of addresses in this heap theory.
   */
  val AddressSort : Sort

  /**
   * Sort of address ranges in this heap theory.
   */
  val AddressRangeSort : Sort

  /**
   * Sort of objects stored on the heap. This sort is one of the elements
   * of <code>userHeapSorts</code>.
   */
  val ObjectSort : Sort

  /**
   * Result sort of the allocation function.
   */
  val AllocResSort : Sort

  /**
   * Result sort of the batch allocation function.
   */
  val BatchAllocResSort : Sort

  /**
   * Sorts declared as part of the heap ADT.
   */
  val userHeapSorts : IndexedSeq[Sort]

  /**
   * The index of the <code>ObjectSort</code> among the
   * <code>userHeapSorts</code>.
   */
  lazy val objectSortIndex : Int = userHeapSorts indexOf ObjectSort

  /**
   * User-specified constructor declarations.
   */
  val userHeapCtorSignatures : Seq[(String, Heap.CtorSignature)]

  /**
   * Constructors declared as part of the heap ADT.
   */
  val userHeapConstructors : IndexedSeq[MonoSortedIFunction]

  /**
   * Selectors declared as part of the heap ADT.
   */
  val userHeapSelectors : IndexedSeq[Seq[MonoSortedIFunction]]

  /**
   * Updators declared as part of the heap ADT.
   */
  val userHeapUpdators : IndexedSeq[Seq[MonoSortedIFunction]]

  /**
   * Tester for the user-declared heap constructors.
   * The ids expected by the tester coincide with the
   * positions in the sequence <code>userHeapCtors</code>.
   */
  def hasUserHeapCtor(t : ITerm, id : Int) : IFormula

  /**
   * Constant representing empty heaps.
   */
  val emptyHeap : IFunction             //  -> Heap

  /**
   * Constant representing the null address.
   */
  val nullAddr : IFunction              //  -> Address

  /**
   * Function to allocate new objects on the heap.
   */
  val alloc : IFunction                 // Heap x Object -> AllocRes

  /**
   * Function to obtain the new heap after allocation.
   */
  val allocResHeap : IFunction          // AllocRes -> Heap

  /**
   * Function to obtain the new address after allocation.
   */
  val allocResAddr : IFunction          // AllocRes -> Address

  /**
   * Function to allocate a sequence of objects on the heap.
   */
  val batchAlloc : IFunction            // Heap x Object x Int -> BatchAllocRes

  /**
   * Function to obtain the new heap after batch allocation.
   */
  val batchAllocResHeap : IFunction     // BatchAllocRes -> Heap

  /**
   * Function to obtain the new address range after batch allocation.
   */
  val batchAllocResAddr : IFunction     // BatchAllocRes -> AddressRange

  /**
   * Function to read from the heap.
   */
  val read : IFunction                  // Heap x Address -> Object

  /**
   * Function to write to the heap.
   */
  val write : IFunction                 // Heap x Address x Object -> Heap

  /**
   * Function to overwrite objects within an address range.
   */
  val batchWrite : IFunction            // Heap x AddressRange x Object -> Heap

  /**
   * Predicate to test whether an address is valid (allocated and non-null)
   * in a given heap.
   */
  val valid : Predicate                 // Heap x Address -> Bool

  /**
   * Predicate to test whether an address is valid (allocated and non-null)
   * in a given heap. Synonym for <code>valid</code>.
   */
  def isAlloc : Predicate = valid

  /**
   * A function to enumerate the addresses that can be used on this heap.
   * <code>nthAddr(1)</code> is the address returned by the first call to
   * <code>alloc</code>, <code>nthAddr(2)</code> the second address, etc.
   * Applying the function to zero or to negative values should be treated
   * as a synonym for <code>nullAddr</code>.
   */
  val nthAddr : IFunction               // Nat1 -> Address

  /**
   * A function to enumerate range of the addresses that can be used on this
   * heap. <code>nthAddrRange(1, n)</code> is a range of addresses starting
   * at the address <code>nthAddr(1)</code> of size <code>n</code>. Applying
   * the function to a start address that is not positive or size that is not
   * non-negative should be interpreted as an empty address range.
   */
  val nthAddrRange : IFunction          // Nat1 x Nat -> Address

  /**
   * Function to obtain the n'th address in an address range. Accessing
   * addresses outside of the range will return <code>nullAddr</code>.
   */
  val addressRangeNth : IFunction       // AddressRange x Int -> Address

  /**
   * Function to obtain the number of addresses in an address range.
   */
  val addressRangeSize : IFunction       // AddressRange -> Nat

  /**
   * Predicate to test whether an address belongs to an address range.
   */
  val addressRangeWithin : Predicate    // AddressRange x Address -> Bool

  /**
   * The object stored on the heap at not yet allocated locations.
   */
  val defaultObject : ITerm

}