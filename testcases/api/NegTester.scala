

//package ap

import ap.parser._
import ap.SimpleAPI
import ap.theories.ADT
import ap.util.Debug
import ap.types.Sort

/**
 * Test correct SMT-LIB pretty-printing of ADT testers.
 */
object NegTester extends App {

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    import ADT._

    Debug enableAllAssertions true

    val listADT =
      new ADT (List("list"),
               List(("nil",  CtorSignature(List(), ADTSort(0))),
                    ("cons", CtorSignature(List(("head", OtherSort(Sort.Integer)),
                                                ("tail", ADTSort(0))),
                                           ADTSort(0)))))

    val Seq(nil, cons) = listADT.constructors
    val Seq(_, Seq(head, tail)) = listADT.selectors

    val c = createConstant("c", listADT.sorts(0))

    addTheory(listADT)

    println(smtPP(listADT.hasCtor(c, 0)))
    println(smtPP(!listADT.hasCtor(c, 0)))

    println(smtPP(asIFormula(asConjunction(listADT.hasCtor(c, 0)))))
    println(smtPP(asIFormula(asConjunction(!listADT.hasCtor(c, 0)))))
  }

}
