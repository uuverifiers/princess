


package ap.theories.arrays


import ap.SimpleAPI
import ap.parser._


object SetTest extends App {

  import IExpression._

  SimpleAPI.withProver { p =>
    import p._

    val setTheory = new SetTheory(Sort.Integer)
    addTheory(setTheory)

    val s = createConstant("s", setTheory.sort)
    val t = createConstant("t", setTheory.sort)
    val u = createConstant("u", setTheory.sort)

    val x = createConstant("x")
    val y = createConstant("y")

    !! (setTheory.contains(s, x))
    !! (!setTheory.contains(s, y))
    !! (u === setTheory.union(s, t))

    println(???)
    println(partialModel)

  }

}
