

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.theories.arrays._

object PairTest extends App {

  ap.util.Debug.enableAllAssertions(true)

  import IExpression._

  val (pairSort, pair, Seq(f1, f2)) =
    ADT.createRecordType("pair", List(("f1", Sort.Integer),
                                      ("f2", Sort.Integer)))

  val vectorOps = Vector(
    CombArray.CombinatorSpec("mask", List(0, 1), 0,
                             (eqZero(v(1)) & (v(2) === v(0))) |
                             (!eqZero(v(1)) & (v(2) === 0))),
    CombArray.CombinatorSpec("zip", List(0, 0), 2,
                             v(2) === pair(v(0), v(1)))
  )

  val VTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Sort.Integer),
                         new ExtArray(List(Sort.Integer), Sort.Bool),
                         new ExtArray(List(Sort.Integer), pairSort)),
                  vectorOps)

  val Seq(intArray, boolArray, pairArray) = VTheory.arraySorts
  val Seq(mask, zip)                      = VTheory.combinators
  val int_select                          = VTheory.subTheories(0).select
  val bool_select                         = VTheory.subTheories(1).select
  val pair_select                         = VTheory.subTheories(2).select

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(VTheory)

    val a = createConstant("a", intArray)
    val b = createConstant("b", boolArray)
    val c = createConstant("c", intArray)
    val d = createConstant("d", pairArray)

    val q = createConstant("q", pairSort)

    scope {
      !! (c === mask(a, b))
      !! (int_select(a, 42) > 0)

      scope {
        !! (bool_select(b, 42) === 0)
        ?? (int_select(c, 42) > 0)
        println(???) // valid
      }

      !! (bool_select(b, 42) === 1)

      scope {
        ?? (int_select(c, 42) > 0)
        println(???) // invalid
        withCompleteModel { eval =>
          for (x <- List(a, b, c))
            println("" + x + " = " + eval(x))
        }
      }

      scope {
        !! (bool_select(b, 41) === 0)
        println(???)
        withCompleteModel { eval =>
          for (x <- List(a, b, c))
            println("" + x + " = " + eval(x))
        }
      }

      scope {
        !! (d === zip(a, c))
        !! (q === pair_select(d, 42))
        ?? (f1(q) > 0 & f2(q) === 0)
        println(???) // valid
      }
//    println(evalToTerm(q))
    }

    scope {
      !! (q === pair(1, 2))
      println(???) // Sat
//      println(partialModel)
    }

  }

}
