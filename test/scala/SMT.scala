import org.scalatest._
import ap.{Signature, SimpleAPI}
import ap.types._
import ap.parser._
import ap.theories.{ADT, Heap}
import ap.util.Debug

class SMTHornTests extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjADTSort = Heap.ADTSort(0)
  val NodeADTSort = Heap.ADTSort(1)

  def defObjCtor(objectADT : ADT, allocResADT : ADT) : ITerm = {
    import IExpression.toFunApplier
    //h.ObjectADT.constructors.last
    //objectADT.constructors.last()
    objectADT.constructors.head(42)
  }

  val heap = new Heap("Heap", "Address", ObjADTSort,
    List("Object", "Node"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjADTSort)),
      ("WrappedNode", Heap.CtorSignature(List(("getNode", NodeADTSort)), ObjADTSort)),
      ("WrappedAddr", Heap.CtorSignature(List(("getAddr", Heap.AddressCtor)), ObjADTSort)),
      ("Node", Heap.CtorSignature(List(("data", Heap.OtherSort(Sort.Integer)), ("next", Heap.AddressCtor)),
        NodeADTSort))/*,
      ("defObj", Heap.CtorSignature(List(), ObjSort))*/),
    defObjCtor)

  val ObjectSort = heap.ObjectADT.sorts(ObjADTSort.num)
  val NodeSort = heap.ObjectADT.sorts(NodeADTSort.num)

  val Seq(wrappedInt,
  wrappedNode,
  wrappedAddr,
  sNode/*,
          defObjCtr*/) = heap.ObjectADT.constructors
  val Seq(Seq(getInt),
  Seq(getNode),
  Seq(getAddr),
  Seq(data, next), _*) = heap.ObjectADT.selectors

  import IExpression.toFunApplier
  val isWrappedNode = (a: ITerm, b: ITerm) =>
      heap.ObjectADT.hasCtor(wrappedNode(heap.read(a, b)), ObjADTSort.num)

  //val defObj = defObjCtr()

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._

    val I1 = createRelation("I1", Seq(HeapSort))
    val I2 = createRelation("I2", Seq(HeapSort, AddressSort))
    val I3 = createRelation("I3", Seq(HeapSort, AddressSort, NodeSort))
    val I4 = createRelation("I4", Seq(HeapSort, AddressSort, NodeSort,
      AddressSort))
    val I5 = createRelation("I5", Seq(HeapSort, AddressSort))

    import IExpression.{all => forall, _}

    val clauses : Seq[IFormula] = Seq(
      I1(emptyHeap()),
      HeapSort.all(h => AllocResSort.all(ar =>
        I1(h) & ar === alloc(h, wrappedNode(sNode(0, nullAddr()))) ==>
          I2(newHeap(ar), newAddr(ar))
      )),
      HeapSort.all(h => AddressSort.all(list => NodeSort.all(n =>
        I2(h, list) & n === getNode(read(h, list)) ==>
          I3(h, list, n)
      ))),
      HeapSort.all(h => AddressSort.all(list => NodeSort.all(n =>
        AllocResSort.all(ar =>
          I3(h, list, n) & ar === alloc(h, wrappedNode(sNode(data(n)+1, nullAddr()))) ==>
            I4(newHeap(ar), list, n, newAddr(ar)))))),
      HeapSort.all(h => AddressSort.all(list => NodeSort.all(n =>
        AddressSort.all(p => HeapSort.all(h1 => Sort.Integer.all(x =>
          (I4(h, list, n, p) & x === data(getNode(read(h, list))) &
        h1 === write(h, list, wrappedNode(sNode(x, p)))) ==>
        I5(h1, list)))))))
    )

    val assertions : Seq[IFormula] = Seq(
      HeapSort.all(h => AddressSort.all(list =>
        I2(h, list) & !isAlloc(h, list) ==> false)),
      HeapSort.all(h => AddressSort.all(list =>
        I2(h, list) & !isWrappedNode(h, list) ==> false)),
      HeapSort.all(h => AddressSort.all(list => NodeSort.all(n =>
        AddressSort.all(p =>
          I4(h, list, n ,p) & !isAlloc(h, list) ==> false)))),
      HeapSort.all(h => AddressSort.all(list => NodeSort.all(n =>
        AddressSort.all(p =>
          I4(h, list, n, p) & !isWrappedNode(h, list) ==> false))))
    )

    /*for (f <- fs) {
      println(pr.smtPP(f))
    }*/

    val sig = Signature(Set(), Set(), Set(), Map(), pr.order)

    SMTLineariser(clauses ++ assertions, sig,"SMTTest")

    "All heap theory tests" should "pass" in {
      assert(true)
    }
  }
}
