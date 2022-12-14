
package ap.theories.arrays

import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ADT.BoolADT.{True, False}

object CartTest extends App {

  ap.util.Debug.enableAllAssertions(true)

  import IExpression._

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(0) + v(1) === v(2)),
    CombArray.CombinatorSpec("vec_minus", List(0, 0), 0,
                             v(0) - v(1) === v(2))
  )

  def bools(n : Int) = for (_ <- 0 until n) yield Sort.Bool

  val CartTheory =
    new CartArray(bools(3), Sort.Integer, 2, vectorOps)
  
  val array3 = CartTheory.extTheories(bools(3))
  val array2 = CartTheory.extTheories(bools(2))

  def proj3(k : Int) = CartTheory.projections((bools(3), k))

  val array2Comb = CartTheory.combTheories(bools(2))
  val Seq(vec_plus2, vec_minus2) = array2Comb.combinators

  // Initial version of Hadamart. Missing is the sqrt(2) factor
  def Rot(k : Int, x : ITerm, y : ITerm) : IFormula =
    array2.sort.ex((xF, xT) =>
      xF === proj3(k)(x, False) &
      xT === proj3(k)(x, True) &
      proj3(k)(y, False) === vec_plus2(xF, xT) &
      proj3(k)(y, True) === vec_minus2(xF, xT)
    )

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(CartTheory)

    val a = createConstant("a", array3.sort)
    val b = createConstant("b", array3.sort)
    val c = createConstant("c", array3.sort)

    scope {
      val aF = createConstant("aF", array2.sort)
      val aT = createConstant("aT", array2.sort)

      !! (aF === proj3(0)(a, False))
      !! (aT === proj3(0)(a, True))

      scope {
        !! (array3.select(a, False, True, False) > 0)
        ?? (array2.select(aF, True, False) > 0)
        println(???) // valid
      }

      !! (proj3(0)(b, False) === vec_plus2(aF, aT))
      !! (proj3(0)(b, True)  === vec_minus2(aF, aT))

      scope {
        !! (array3.select(a, False, True, False) > 0)
        !! (array3.select(a, True,  True, False) > 0)
        ?? (array3.select(b, False, True, False) > 0)
        println(???) // valid
      }
    }

    scope {
      !! (Rot(1, a, b))
      !! (Rot(2, b, c))
      println(???) // sat
//      println(partialModel)        // does not work yet
//      println(evalToTerm(a))
    }
  }

}
