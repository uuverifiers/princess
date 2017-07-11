/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

import ap._
import ap.parser._
import ap.theories._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience, TermOrder}
import ap.terfor.preds.Atom
import ap.proof.goal.Goal


/**
 * Simple theory implementing associativity of a function symbol f.
 * This is done by: 1. using a triggered axiom to turn right-associative
 * occurrences into left-associative occurrences, and 2. using a plug-in
 * that eliminates remaining right-associative occurrences from goals.
 */
object ATheory extends Theory {
  import IExpression._

  val f = new IFunction("f", 2, true, false)
  val functions = List(f)

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms =
                       all(x => all(y => all(z =>
                           trig(f(f(x, y), z) === f(x, f(y, z)),
                              f(x, f(y, z)))))))
  val Seq(_f) = predicates
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = Set()
  val functionalPredicates = predicates.toSet
  val functionPredicateMapping = List(f -> _f)

  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val fAtoms = goal.facts.predConj.positiveLitsWithPred(_f)

      val atomsToRemove =
        for (a1 <- fAtoms.iterator;             // f(a,   f(b, c))
             a2 <- fAtoms.iterator;             // a1     a2
             if (a1(1) == a2(2) &&
                 (fAtoms exists {               // f(  f(a, b), c)
                    a3 => a3(1) == a2(1) &&     // a3  a4
                          a3(2) == a1(2) &&
                          (fAtoms exists {
                             a4 => a4(0) == a1(0) &&
                                   a4(1) == a2(0) &&
                                   a4(2) == a3(0)
                  })}))) yield a1

      val factsToRemove = Conjunction.conj(atomsToRemove, goal.order)
      if (factsToRemove.isTrue)
        List()
      else
        List(Plugin.RemoveFacts(factsToRemove))
    }
  })

  TheoryRegistry register this
}

////////////////////////////////////////////////////////////////////////////////

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._
  import ATheory.f

  val a = createConstant("a")
  val x = createConstants(15)

  scope {
    val left = x reduceLeft (f(_, _))
    val right = x reduceRight (f(_, _))

    !! (left >= a)
    !! (right < a)
    println(???)
  }

}
