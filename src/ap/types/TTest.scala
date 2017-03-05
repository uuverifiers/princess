package ap.types

import ap.parser._
import ap.SimpleAPI

object TTest extends App {

  val p = SimpleAPI.spawnWithAssertions
  import p._
  import IExpression._

  println("Starting")

  val x = createConstant("x")
  val y = createConstant("y")

  scope {
    val f = ex((a, b) => a === x + b)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat ex (_ === x)
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = Sort.Nat all { a => x === a }
    println(pp(f))
    !! (f)
    println(???)
  }

  scope {
    val f = (Sort.Nat ex { a => x === y + a }) <===> (y <= x)
    println(pp(f))
    ?? (f)
    println(???)
  }

  println("Finished")

}