



import ap.SimpleAPI
import ap.parser._
import ap.theories.rationals.Rationals
import ap.theories.arrays._


object RatTest extends App {

  import IExpression._

  ap.util.Debug.enableAllAssertions(true)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             Rationals.plus(v(0, Rationals.dom),
                                            v(1, Rationals.dom)) ===
                               v(2, Rationals.dom)),
    CombArray.CombinatorSpec("vec_times", List(0, 0), 0,
                             Rationals.mul(v(0, Rationals.dom),
                                           v(1, Rationals.dom)) ===
                               v(2, Rationals.dom))
  )

  val VectorTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Rationals.dom)),
                  vectorOps)

  val Seq(ratVector)           = VectorTheory.arraySorts
  val Seq(vec_plus, vec_times) = VectorTheory.combinators
  val vec_select               = VectorTheory.subTheories(0).select
  val vec_const                = VectorTheory.subTheories(0).const

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    // currently leading to an exception
    addTheory(VectorTheory)

    val x = createConstant("x")
    val v = createConstant("v", ratVector)
    val w = createConstant("w", ratVector)

    scope {
      !! (Rationals.gt(vec_select(v, 2), Rationals.zero))
      println(???)

      !! (w === vec_plus(v, vec_const(Rationals.one)))
      println(???)

      !! (Rationals.lt(vec_select(w, 2), Rationals.one))
      println(???)
    }

    scope {
      !! (v === vec_const(Rationals.one))
      !! (w === vec_plus(v, v))
      ?? (vec_select(w, x) === Rationals.int2ring(2))
      println(???)
    }

    scope {
      ?? (vec_plus(vec_const(Rationals.int2ring(2)),
                   vec_const(Rationals.int2ring(2))) ===
            vec_times(vec_const(Rationals.int2ring(2)),
                      vec_const(Rationals.int2ring(2))))
      println(???)
    }
  }

}
