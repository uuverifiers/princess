


package ap.theories.arrays


import ap.SimpleAPI
import ap.parser._


object SetTest extends App {

  import IExpression._

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val setTheory = new SetTheory(Sort.Integer)
    addTheory(setTheory)

    import setTheory.{contains, subsetOf, union, isect, compl, set, emptySet}

    val s = createConstant("s", setTheory.sort)
    val t = createConstant("t", setTheory.sort)
    val u = createConstant("u", setTheory.sort)
    val v = createConstant("v", setTheory.sort)

    val x = createConstant("x")
    val y = createConstant("y")
    val z = createConstant("z")

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

    scope {
      ?? (set(x, y) === emptySet)
      println(???) // invalid
    }

    scope {
      ?? ((set(x, y) === set(x)) <=> (x === y))
      println(???) // valid
    }

    scope {
      !! (set(x, y, z) === set(1, 2, 3))
      println(???) // sat
      ?? (x > 0)
      println(???) // valid
    }

    scope {
      !! (union(union(set(1), set(2)), union(set(3), set(4))) ===
          union(union(set(1), set(2)), union(set(3), set(5))))
      println(???) // unsat
    }

  }

}
