import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.{ADT, Heap}
import ap.util.Debug

class HeapTheoryTests extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)

  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "struct_S"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", Heap.CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("WrappedAddr", Heap.CtorSignature(List(("getAddr", Heap.AddressCtor)), ObjSort)),
      ("struct_S", Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))),
        StructSSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectADT : ADT, allocResADT : ADT) : ITerm = {
    import IExpression.toFunApplier
    objectADT.constructors.last()
  }

  val Seq(wrappedInt,
          wrappedS,
          wrappedAddr,
          struct_S,
          defObjCtr) = heap.ObjectADT.constructors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(getAddr),
          Seq(sel_x), _*) = heap.ObjectADT.selectors

  import IExpression.toFunApplier
  val defObj = defObjCtr()

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._

    val h = createConstant("h", HeapSort)
    val h1 = createConstant("h'", HeapSort)
    val p =  createConstant("p", AddressSort)
    val p1 =  createConstant("p'", AddressSort)
    val ar = createConstant("ar", AllocResSort)
    val ar1 = createConstant("ar'", AllocResSort)
    val o = createConstant("o", ObjectSort)
    val o1 = createConstant("o'", ObjectSort)

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModels = true,
      printModelOnlyOnFail = false,
      printOnlyOnFail = false)
    import priTests._

    TestCase (
      "All locations on the empty heap are unallocated.",
      UnsatStep(isAlloc(emptyHeap(), p)),
      SatStep(!isAlloc(emptyHeap(), p))
    )

    TestCase (
      "For all heaps, null pointer always points to an unallocated location.",
      UnsatStep(isAlloc(h, nullAddr()))
    )

    TestCase(
      "For all heaps, trying to read the null pointer returns the defined " +
      "object.",
      UnsatStep(read(h, nullAddr()) =/= defObj),
      SatStep(read(h, nullAddr()) === defObj)
    )

    TestCase(
      "For all heaps, writing to the null pointer returns the original heap.",
      UnsatStep(write(h, nullAddr(), o) =/= h),
      SatStep(write(h, nullAddr(), o) === h)
    )

    TestCase (
      "After alloc, the returned pointer points to an allocated address.",
      CommonAssert(alloc(h, o) === ar),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      UnsatStep(!isAlloc(newHeap(ar), newAddr(ar)))
    )

    TestCase (
      "After alloc, previously allocated addresses are the same in both heaps.",
      CommonAssert(
        alloc(h, o) === ar
      ),
      UnsatStep(
        isAlloc(h, p) & !isAlloc(newHeap(ar), p)
      ),
      UnsatStep(
        p =/= newAddr(ar),
        !isAlloc(h, p),
        isAlloc(newHeap(ar), p)
      )
    )

    TestCase(
      "Deterministic allocation",
      UnsatStep(
        forall(List(AddressSort), isAlloc(h, v(0)) <=> isAlloc(h1, v(0))),
        alloc(h, o) === ar,
        alloc(h1, o1) === ar1,
        newAddr(ar) =/= newAddr(ar1)
      )
    )

    /** Test cases for facts about read/write */
    TestCase(
      "Reading from a previously written (alloc.) " +
      "location returns that value.",
      CommonAssert(
        isAlloc(h, p)
      ),
      SatStep(
        read(write(h, p, o), p) === o
      ),
      UnsatStep(
        read(write(h, p, o), p) =/= o
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value",
      CommonAssert(
        ar === alloc(h, o)
      ),
      SatStep(
        read(newHeap(ar), newAddr(ar)) === o
      ),
      UnsatStep(
        read(newHeap(ar), newAddr(ar)) =/= o
      )
    )

    TestCase(
      "Allocation does not modify any of the values on the old heap",
      CommonAssert(
        ar === alloc(h, o),
        p =/= newAddr(ar)
      ),
      SatStep(
        read(newHeap(ar), p) === read(h, p)
      ),
      UnsatStep(
        read(newHeap(ar), p) =/= read(h, p)
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value (v2)",
      CommonAssert(
        alloc(h, o) === ar,
        h1 === newHeap(ar),
        p === newAddr(ar)
      ),
      SatStep(
        read(h1, p) === o
      ),
      UnsatStep(
        read(h1, p) =/= o
      )
    )

    TestCase(
      "Reading an unallocated location returns the defined object",
      CommonAssert(
        !isAlloc(h, p)
      ),
      SatStep(
        read(h, p) === defObj
      ),
      UnsatStep(
        read(h, p) =/= defObj
      )
    )

    TestCase(
      "Writing to a location does not modify the rest of the locations",
      CommonAssert(
        p =/= p1,
        isAlloc(h, p),
        isAlloc(h, p1)
      ),
      SatStep(
        read(write(h, p1, o), p) === read(h, p)
      ),
      UnsatStep(
        read(write(h, p1, o), p) =/= read(h, p)
      )
    )

    TestCase(
      "Writing to an unallocated location returns the same heap.",
      CommonAssert(!isAlloc(h, p)),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(h =/= emptyHeap()),
      SatStep(write(h, p, o) === h & h =/= emptyHeap()),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(p =/= nullAddr()),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h)
    )

    TestCase(
      "Allocating and dereferencing pointer to pointer.",
      CommonAssert(alloc(emptyHeap(), wrappedInt(42)) === ar &
                   p === newAddr(ar) & h === newHeap(ar)),
      CommonAssert(alloc(h, wrappedAddr(p)) === ar1 &
                   p1 === newAddr(ar1) & h1 === newHeap(ar1)),
      SatStep(read(h, getAddr(read(h1,p1))) === wrappedInt(42)),
      UnsatStep(read(h, getAddr(read(h1,p1))) =/= wrappedInt(42))
    )

  TestCase(
      "Extensionality over write",
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (exclude empty heaps)",
      CommonAssert(h =/= emptyHeap()),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (exclude empty heaps and null addresses)",
      CommonAssert(h =/= emptyHeap() &
                   p =/= nullAddr()),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality over write (only valid writes)",
      CommonAssert(isAlloc(h, p)),
      SatStep(write(h, p, o) === write(write(h, p, o1), p, o)),
      UnsatStep(write(h, p, o) =/= write(write(h, p, o1), p, o))
    )

    TestCase(
      "Extensionality",
      CommonAssert(counter(h) === counter(h1) &
                   h =/= h1),
      SatStep(AddressSort.ex(a =>
        isAlloc(h, a) & (read(h, a) =/= read(h1, a)))),
      UnsatStep(AddressSort.all(a =>
        isAlloc(h, a) & (read(h, a) === read(h1, a))))
    )

    "All heap theory tests" should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
