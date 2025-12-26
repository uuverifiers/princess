/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer, Zafer Esen
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

import ap.theories.ADT
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parameters.{GlobalSettings, Param}
import ap.parameters.Param.InputFormat
import ap.types._
import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._

class ArrayHeapTests3 extends Properties("ArrayHeapTests3") {
  import Heap._
  import HeapTests.measureTime

  Debug enableAllAssertions false

  val NullObjName = "NullObj"
  val ObjSort = ADTSort(0)

  val sorts =
    List("HeapObject")

  val ctors =
    List(
        ("WrappedInt", CtorSignature(List(("getInt",
          OtherSort(Sort.Integer))), ObjSort)),
        ("WrappedAddr", CtorSignature(List(("getAddr", AddrSort)), ObjSort)),
        ("defObj", CtorSignature(List(), ObjSort)))

  def defObjCtor(objectCtors : Seq[IFunction]) : ITerm = {
      import IExpression.toFunApplier
      objectCtors.last()
    }

  def createArrayHeap : Heap =
    new ArrayHeap(
      "heap", "addr", "addrRange", ObjSort, sorts, ctors, defObjCtor)

  def createNativeHeap : Heap =
    new NativeHeap(
      "heap", "addr", "addrRange", ObjSort, List("HeapObject"), ctors, defObjCtor)

  import IExpression.toFunApplier

  val N = 10

  property("writes") = Console.withOut(ap.CmdlMain.NullStream) {
  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._

    val heap = createArrayHeap
    import heap._

    val wrappedInt = heap.userHeapConstructors.head

    val hs = createConstants(N, HeapSort)
    val hs2 = createConstants(N, HeapSort)
    val as = createConstants(N, AddressSort)

    measureTime("Allocation") {
      for (n <- 1 until N)
        !! (as(n) === heapAddrPair_2(alloc(hs(n - 1), wrappedInt(n))) &
            hs(n) === heapAddrPair_1(alloc(hs(n - 1), wrappedInt(n))))
    }

    checkHeap(heap, pr, hs.last, as)

    true
  }}

  property("batchAlloc") = Console.withOut(ap.CmdlMain.NullStream) {
  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._

    val heap = createArrayHeap
    import heap._

    val wrappedInt = heap.userHeapConstructors.head

    val h0 = createConstant("h0", HeapSort)
    val h = createConstant("h", HeapSort)
    val ar = createConstant("ar", RangeSort)

    measureTime("Allocation") {
      !! (h  === heapRangePair_1(allocRange(h0, wrappedInt(1), N + 1)))
      !! (ar === heapRangePair_2(allocRange(h0, wrappedInt(1), N + 1)))
    }

    checkHeap(heap, pr, h, rangeNth(ar, _))

    true
  }}

  def checkHeap(heap : Heap, pr : SimpleAPI,
                initHeap : ITerm, as : Int => ITerm) : Unit = {
    import heap._
    import pr._

    val wrappedInt = heap.userHeapConstructors.head
    val Seq(getInt) = heap.userHeapSelectors.head

    val hs2 = createConstants(N, HeapSort)

    measureTime("Check 1") {
      println(???)
    }

    measureTime("Updating heap") {
      !! (hs2(0) === initHeap)
      for (n <- 1 until N)
        !! (hs2(n) === write(hs2(n-1), as(n),
	                     wrappedInt(getInt(read(hs2(n-1), as(n))) + 1)))
    }

    val h2 = hs2.last
    
    measureTime("Check 2") {
      println(???)
    }

    measureTime("Conjecture") {
      ?? (getInt(read(h2, as(1))) > 0)
    }

    measureTime("Check 3") {
      println(???)
    }
  }

}
