



import ap.SimpleAPI
import ap.parser._
import ap.theories.GroebnerMultiplication
import ap.theories.arrays._

object VectorTest extends App {

  import IExpression._

  ap.util.Debug.enableAllAssertions(true)

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(0) + v(1) === v(2)),
    CombArray.CombinatorSpec("vec_times", List(0, 0), 0,
                             GroebnerMultiplication.mul(v(0), v(1)) === v(2))
  )

  val VectorTheory =
    new CombArray(Vector(new ExtArray(List(Sort.Integer), Sort.Integer)),
                  vectorOps, List(GroebnerMultiplication))

  val Seq(intVector)           = VectorTheory.arraySorts
  val Seq(vec_plus, vec_times) = VectorTheory.combinators
  val vec_select               = VectorTheory.subTheories(0).select
  val vec_store                = VectorTheory.subTheories(0).store
  val vec_const                = VectorTheory.subTheories(0).const

  def vec(ts : ITerm*) : ITerm = {
    var res : ITerm = vec_const(0)
    for ((t, n) <- ts.zipWithIndex)
      res = vec_store(res, n, t)
    res
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    addTheory(VectorTheory)

    val x = createConstant("x")
    val y = createConstant("y")
    val z = createConstant("z")
    val v = createConstant("v", intVector)
    val w = createConstant("w", intVector)

    scope {
      !! (vec_select(v, 2) > 0)
      println(???) // sat

      !! (w === vec_plus(v, vec_const(10)))
      println(???) // sat

      withCompleteModel { eval =>
        for (x <- List(v, w))
          println("" + x + " = " + eval(x))
      }

      !! (vec_select(w, 2) < 2)
      println(???) // unsat
    }

    scope {
      !! (v === vec_const(1))
      !! (w === vec_plus(v, v))
      ?? (vec_select(w, x) === 2)
      println(???) // valid
    }

    scope {
      ?? (vec_plus(vec_const(2), vec_const(2)) ===
            vec_times(vec_const(2), vec_const(2)))
      println(???) // valid
    }

    scope {
      val a = vec(x, y, z)
      val b = vec(3, 2, 1)
      !! (vec_times(a, vec_const(-1)) === b)
      println(???) // sat
    }

    scope {
      !! (v === vec_const(1))
      !! (w === vec_const(3))
      !! (w === vec_plus(v, v))
      println(???) // unsat
    }

    scope {
      val u = createConstant("u", intVector)
      !! (v === vec_const(1))
      !! (w === vec_const(3))
      !! (u === vec_store(w, 0, 3))
      !! (u === vec_plus(v, v))
      println(???) // unsat
    }
  }

}
