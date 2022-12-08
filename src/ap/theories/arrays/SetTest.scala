


package ap.theories.arrays


import ap.SimpleAPI
import ap.parser._


object SetTest extends App {

  import IExpression._

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val setTheory = new SetTheory(Sort.Integer)
    addTheory(setTheory)

    import setTheory.{contains, subsetOf, union, isect, compl}

    val s = createConstant("s", setTheory.sort)
    val t = createConstant("t", setTheory.sort)
    val u = createConstant("u", setTheory.sort)
    val v = createConstant("v", setTheory.sort)

    val x = createConstant("x")
    val y = createConstant("y")

    !! (contains(s, x))
    !! (!contains(s, y))
    !! (u === union(s, t))

    println(???) // sat
    println(partialModel)

    scope {
      ?? (contains(u, x))
      println(???) // valid
    }

    scope {
      !! (v === isect(s, t))
      !! (contains(v, y))
      println(???) // unsat
    }

    scope {
      ?? (compl(isect(s, t)) === union(compl(s), compl(t)))
      println(???) // valid
    }

    scope {
      ?? (isect(compl(s), compl(t)) === compl(union(s, t)))
      println(???) // valid
    }

    scope {
      ?? (subsetOf(isect(s, t), s) & subsetOf(s, union(s, t)))
      println(???) // valid
    }

    scope {
      ?? ((subsetOf(s, t) & subsetOf(t, s)) <=> (s === t))
      println(???) // valid
    }

    scope {
      ?? ((union(s, t) === isect(s, t)) <=> (s === t))
      println(???) // valid
    }
  }

}
