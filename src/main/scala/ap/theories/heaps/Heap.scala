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

import ap.types.{Sort, MonoSortedIFunction}
import ap.theories.{ADT, Theory}
import ap.parser.{FunctionCollector, IExpression, IFormula, IFunction, ITerm, 
                  SMTLinearisableTheory, SMTLineariser}
import IExpression.Predicate
import ap.parser.SMTLineariser.{asString, quoteIdentifier}

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
  case class OtherSort(sort : Sort) extends CtorArgSort

  /**
   * Reference to the address sort that is specific to the heap to be declared.
   */
  case object AddrSort              extends CtorArgSort

  /**
   * Reference to the address range sort that is specific to the heap to be
   * declared.
   */
  case object RangeSort             extends CtorArgSort

  /**
   * Specification of a heap ADT constructor.
   */
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  /**
   * Extractor to recognise any sort related to a heap theory.
   * This includes the sorts for heaps and addresses, address ranges,
   * user defined ADT sorts, etc.
   */
  object HeapRelatedSort {
    def unapply(s : Sort) : Option[Heap] = synchronized { heapSorts get s }
  }

  /**
   * Extractor to recognise any function related to a heap theory.
   */
  object HeapRelatedFunction {
    def unapply(f : IFunction) : Option[Heap] = synchronized { heapFuns get f }
  }

  /**
   * Extractor to recognise any function related to a heap theory.
   */
  object HeapRelatedPredicate {
    def unapply(p : Predicate) : Option[Heap] = synchronized { heapPreds get p }
  }

  private val heapSorts = new MHashMap[Sort, Heap]
  private val heapFuns  = new MHashMap[IFunction, Heap]
  private val heapPreds = new MHashMap[Predicate, Heap]

  def register(t : Heap) : Unit = synchronized {
    heapSorts.put(t.HeapSort,          t)
    heapSorts.put(t.AddressSort,       t)
    heapSorts.put(t.RangeSort, t)
    heapSorts.put(t.AllocResSort,      t)
    heapSorts.put(t.BatchAllocResSort, t)

    for (s <- t.userHeapSorts)
      heapSorts.put(s, t)

    val (funs, preds) = t.heapRelatedSymbols
    
    for (f <- funs)
      heapFuns.put(f, t)
    for (p <- preds)
      heapPreds.put(p, t)
  }

  object Names {
    val Empty        = "heap.empty"
    val Null         = "heap.null"
    val Addr         = "heap.addr"
    val Range        = "heap.range"

    val Alloc        = "heap.alloc"
    val Alloc1       = "heap.alloc_first"
    val Alloc2       = "heap.alloc_second"

    val AllocRange   = "heap.allocRange"
    val AllocRange1  = "heap.allocRange_first"
    val AllocRange2  = "heap.allocRange_second"

    val Read         = "heap.read"
    val Write        = "heap.write"
    val WriteRange   = "heap.writeRange"
    val Valid        = "heap.valid"
    val NextAddr     = "heap.nextAddr"

    val RangeNth     = "heap.rangeNth"
    val RangeSize    = "heap.rangeSize"
    val RangeStart   = "heap.rangeStart"
    val RangeWithin  = "heap.rangeWithin"

    def Pair(first : String, second : String) = first + second + "Pair"
  }

}

/**
 * Trait implemented by the different heap theories.
 */
trait Heap extends Theory with SMTLinearisableTheory {

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
  val RangeSort : Sort

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
  val batchAllocResAddr : IFunction     // BatchAllocRes -> Range

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
  val batchWrite : IFunction            // Heap x Range x Object -> Heap

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
   * A function to enumerate the next addresses that will be returned by
   * the <code>alloc</code> function. The next address that can be
   * allocated is <code>nextAddr(h, 0)</code>, then
   * <code>nextAddr(h, 1)</code>, etc. Applying the function to negative
   * integers returns the last addresses that have been allocated:
   * <code>nextAddr(h, -1)</code> is the last address that has been allocated
   * on <code>h</code>, <code>nextAddr(h, -2)</code> the address before that,
   * etc. Since a heap only has finitely many allocated addresses,
   * for two small <code>n</code>, the result of <code>nextAddr(h, n)</code>
   * is <code>nullAddr</code>.
   * 
   * <code>nthAddr(k)</code> is a synonym for
   * <code>nextAddr(emptyHeap, k - 1)</code>.
   */
  val nextAddr : IFunction              // Heap x Int -> Address

  /**
   * A function to enumerate range of the addresses that can be used on this
   * heap. <code>nthRange(1, n)</code> is a range of addresses starting
   * at the address <code>nthAddr(1)</code> of size <code>n</code>. Applying
   * the function to a start address that is not positive or size that is not
   * non-negative should be interpreted as an empty address range.
   */
  val nthRange : IFunction               // Nat1 x Nat -> Range

  /**
   * Function to obtain the n'th address in an address range. Accessing
   * addresses outside of the range will return <code>nullAddr</code>.
   */
  val rangeNth : IFunction               // Range x Int -> Address

  /**
   * Function to obtain the number of addresses in an address range.
   */
  val rangeSize : IFunction              // Range -> Nat

  /**
   * Predicate to test whether an address belongs to an address range.
   */
  val rangeWithin : Predicate           // Range x Address -> Bool

  /**
   * The object stored on the heap at not yet allocated locations.
   */
  val defaultObject : ITerm

  /**
   * Method to query all functions and predicates of the theory,
   * including API, internal symbols, and symbols of the constituent theories.
   */
  def heapRelatedSymbols : (Set[IFunction], Set[Predicate])

  //////////////////////////////////////////////////////////////////////////////
  /**
   * Overrides to make Heap SMT-linearisable
   */

  override def printSMTDeclaration : Unit = {
    import SMTLineariser.{asString, quoteIdentifier}

    print("(declare-heap ")
    println(HeapSort.name + " " + AddressSort.name + " " +
            RangeSort.name + " " + ObjectSort.name)
    println(" " ++ asString(defaultObject))
    print(" (")
    print((for(s <- userHeapSorts)
      yield ("(" + quoteIdentifier(s.name) + " 0)")) mkString " ")
    println(") (")
    for (_ <- userHeapSorts) {
      println("  (")
      for ((f, sels) <- userHeapConstructors zip userHeapSelectors) {
        print(" ")
        ADT.printSMTCtorDeclaration(f, sels)
      }
      println("  )")
    }
    println("))")
  }

  override def SMTDeclarationSideEffects : Seq[Theory] = dependencies.toSeq

}
