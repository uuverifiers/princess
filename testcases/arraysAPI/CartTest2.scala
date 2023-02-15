
import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._

object CartTest2 extends App {

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

  import CartTheory.{proj, sel, sto, arraySto, con}

  val Seq(vec_plus, vec_minus) = CartTheory.combinators

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(CartTheory)

    val a = createConstant("a", array3Sort)
    val b = createConstant("b", array3Sort)
    val c = createConstant("c", array3Sort)
    val d = createConstant("d", array3Sort)

    val x = createConstant("x")
    val y = createConstant("y")

    val bits = createConstants(3, Sort.Bool)

    !! (b === arraySto(a, (1, True)  -> con(bools(2), 42)))
    !! (c === arraySto(b, (0, False) -> con(bools(2), 13)))

    scope {
      !! (x === sel(c, True,  True,  False))
      !! (y === sel(c, False, False, False))

      println(???)
      println(evalToTerm(x))
      println(evalToTerm(y))
    }

    scope {
      !! (sel(b, bits : _*) =/= sel(c, bits : _*))

      println(???)
      println(bits map (evalToTerm(_)))
    }

    scope {
      !! (d === arraySto(c, (0, False) -> proj(b, 0 -> False)))
      !! (sel(d, bits : _*) =/= sel(b, bits : _*))

      println(???)
    }

    scope {
      !! (d === arraySto(arraySto(c,
                    (2, False) -> vec_plus (proj(c, 2 -> True),
                                            proj(c, 2 -> False))),
                    (2, True)  -> vec_minus(proj(c, 2 -> False),
                                            proj(c, 2 -> True))))

      !! (x === sel(d, True,  True,  False))
      !! (y === sel(d, False, False, True))

      println(???)
      println(evalToTerm(x))
      println(evalToTerm(y))
    }
  }

}
