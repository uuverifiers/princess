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
import ap.parameters.Param.InputFormat
import ap.types._
import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._

class HeapTests2 extends Properties("HeapTests2") {
  import HeapTests._
  import Heap._

  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = ADTSort(0)
  val StructSSort = ADTSort(1)
  val heap = new NativeHeap("heap", "addr", "addrRange", ObjSort,
    List("HeapObject", "struct_S"), List(
      ("WrappedInt", CtorSignature(List(("getInt",
        OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("WrappedNode", CtorSignature(List(("getNode", StructSSort)), ObjSort)),
      ("struct_S", CtorSignature(List(("x", OtherSort(Sort.Integer))),
        StructSSort)),
      ("struct_Node", CtorSignature(List(("R", AddrSort)),
        StructSSort)),
      ("defObj", CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectCtors : Seq[IFunction]) : ITerm = {
    import IExpression.toFunApplier
    objectCtors.last()
  }

  val Seq(wrappedInt,
          wrappedS,
          wrappedNode,
          struct_S,
          struct_Node,
          defObj) = heap.userADTCtors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(getNode),
          Seq(sel_x),
          Seq(sel_R),_*) = heap.userADTSels

  property("main") = Console.withOut(ap.CmdlMain.NullStream) {
  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h = HeapSort.newConstant("h")
    val h1 = createConstant("h1", HeapSort)
    val h2 = createConstant("h2", HeapSort)
    val ar = allocResSort.newConstant("ar")
    val p1 =  createConstant("p1", AddressSort)
    val p2 =  createConstant("p2", AddressSort)
    val x = createConstant("x")
    val o = createConstant("o", ObjectSort)


    addConstants(List(h, ar))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr)
    import priTests._

   TestCase (
      "Reading back written value after chain allocation and a write.",
      CommonAssert(
        ar === alloc(newHeap(
                             alloc(emptyHeap(), wrappedInt(0)) // h(0)
                     ), wrappedInt(3))                         // h(0, 3)
      ),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      SatStep(getInt(read(newHeap(ar), newAddr(ar))) === 3),
      UnsatStep(getInt(read(newHeap(ar), newAddr(ar))) =/= 3),
      SatStep(read(newHeap(ar), newAddr(ar)) === wrappedInt(3)),
      CommonAssert(
        h === write(newHeap(ar), newAddr(ar), wrappedInt(50))  // h(0, 50)
      ),
      SatStep(read(h, nthAddr(2)) =/= read(newHeap(ar),nthAddr(2))),
      UnsatStep(read(h, nthAddr(2)) === read(newHeap(ar),nthAddr(2))),
      SatStep(isAlloc(h, newAddr(ar))),
      UnsatStep(getInt(read(h, newAddr(ar))) === 0),
      UnsatStep(getInt(read(h, newAddr(ar))) === 3),
      SatStep(getInt(read(h, newAddr(ar))) =/= 3),
      SatStep(read(h, newAddr(ar)) =/= wrappedInt(3)),
      UnsatStep(getInt(read(h, newAddr(ar))) =/= 50),
      SatStep(getInt(read(h, newAddr(ar))) === 50),
      SatStep(read(h, newAddr(ar)) === wrappedInt(50))
    )

    TestCase(
      "list-001-fail.c-1",
      CommonAssert(h === newHeap(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p1 === newAddr(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p2 === p1),
      SatStep(p1 === p2)
    )
    TestCase(
      "list-001-fail.c-2",
      SatStep(
        h1 === emptyHeap() &&&
        h === newHeap(alloc(h1, wrappedS(struct_S(0)))) &&&
        p1 === newAddr(alloc(h1, wrappedS(struct_S(0)))) &&&
        p2 === p1 &&&
        x === sel_x(getS(read(h, p2)))// &&&
      )
    )
    TestCase(
      "list-004-fail.c",
      SatStep(
        h1 === newHeap(alloc(emptyHeap(), wrappedNode(struct_Node(0)))) &&&
        p1 === newAddr(alloc(emptyHeap(), wrappedNode(struct_Node(0)))) &&&
        h === newHeap(alloc(h1, p1)) &&&
        h2 === write(h, p1, wrappedNode(struct_Node(p1)))
      )
    )

    true
  }}
}
