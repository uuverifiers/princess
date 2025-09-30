package ap

import ap.theories.ADT.BoolADT.True
import ap.theories.ADT.BoolADT.False
import ap.parser._
import ap.theories.arrays._
import IExpression._

object SetTest extends App {

    SimpleAPI.withProver(enableAssert = true) { p =>
        import p._
    
        val setTheory = new SetTheory(Sort.Integer)
        addTheory(setTheory)
    
        import setTheory.{contains, subsetOf, union, isect, compl, set, emptySet}
    
        val a = createConstant("a", setTheory.sort)
        val b = createConstant("b", setTheory.sort)
        val c = createConstant("c", setTheory.sort)
        val d = createConstant("d", setTheory.sort)
    
        import setTheory.arTheory.{select, store, const}

        val empty = const(False)

        // a = {}
        !! (a === empty)
        // b = {0, 1}
        !! (b === store(store(a, 0, True), 1, True))
        // c = {1, 2}
        !! (c === store(store(a, 1, True), 2, True))
    
        println(???) // sat
        println(partialModel)

        scope {
            !! ( d === union(b, c) )
            println(???) // Sat
            println(partialModel)
            // EXCEPTION
        }

    }

}