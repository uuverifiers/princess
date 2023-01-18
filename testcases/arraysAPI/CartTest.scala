
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._

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
  
  val array3Sort = CartTheory.arraySorts(bools(3))
  val array2Sort = CartTheory.arraySorts(bools(2))
  val array1Sort = CartTheory.arraySorts(bools(1))

  import CartTheory.{proj, sel, sto}

  val Seq(vec_plus, vec_minus) = CartTheory.combinators

  // Initial version of Hadamart. Missing is the sqrt(2) factor
  def Rot(k : Int, x : ITerm, y : ITerm) : IFormula =
    array2Sort.ex((xF, xT) =>
      xF === proj(x, k -> False) &
      xT === proj(x, k -> True) &
      proj(y, k -> False) === vec_plus(xF, xT) &
      proj(y, k -> True)  === vec_minus(xF, xT)
    )

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(CartTheory)

    val a = createConstant("a", array3Sort)
    val b = createConstant("b", array3Sort)
    val c = createConstant("c", array3Sort)

    scope {
      val aF = createConstant("aF", array2Sort)
      val aT = createConstant("aT", array2Sort)

      !! (aF === proj(a, 0 -> False))
      !! (aT === proj(a, 0 -> True))

      scope {
        !! (sel(a, False, True, False) > 0)
        ?? (sel(aF, True, False) > 0)
        println(???) // valid
      }

      !! (proj(b, 0 -> False) === vec_plus(aF, aT))
      !! (proj(b, 0 -> True)  === vec_minus(aF, aT))

      scope {
        !! (sel(a, False, True, False) > 0)
        !! (sel(a, True,  True, False) > 0)
        ?? (sel(b, False, True, False) > 0)
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

    scope {
      val a2 = createConstant("a2", array2Sort)
      val b2 = createConstant("b2", array2Sort)
      val x = createConstant("x", array1Sort)
      !! (sel(a, False, False, False) > 0)
      !! (a2 === proj(a,  2 -> False))
      !! (x  === proj(a2, 1 -> False))
      !! (sel(b, False, False, False) < 0)
      !! (b2 === proj(b,  2 -> False))
      !! (x  === proj(b2, 1 -> False))
      println(???) // unsat
    }

    scope {
      val x = createConstant("x", array2Sort)
      val b2 = createConstant("b2", array3Sort)
      val c2 = createConstant("c2", array3Sort)
      !! (b2 === sto(b, False, False, False, 42))
      !! (c2 === sto(c, False, False, False, 43))
      !! (x === proj(b2, 2 -> False))
      !! (x === proj(c2, 2 -> False))
      println(???) // unsat
    }
  }

}
