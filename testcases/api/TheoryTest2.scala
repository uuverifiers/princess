/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

import ap._
import ap.parser._
import ap.theories._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience}
import ap.proof.goal.Goal

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

/**
 * Extremely naive implementation of a theory of non-linear integer arithmetic.
 * Currently the theory only does AC-congruence reasoning for multiplication.
 */
object MulTheory extends Theory {
  import IExpression._

  val mul = new IFunction("mul", 2, true, false)
  val _mul = new Predicate("_mul", 3)

  val functions = List(mul)
  val predicates = List(_mul)
  val axioms = Conjunction.TRUE
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val functionalPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)

  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = {

      type TermMultiset = Map[Term, Int]

      def join(a : TermMultiset, b : TermMultiset) : TermMultiset = {
        var res = a
        for ((t, mult) <- b)
          res = res + (t -> (a.getOrElse(t, 0) + mult))
        res
      }

      // detect _mul facts in the goal

      val termDefs = new MHashMap[Term, MHashSet[TermMultiset]]
      for (a <- goal.facts.predConj.positiveLitsWithPred(_mul))
          termDefs.getOrElseUpdate(a(2), new MHashSet[TermMultiset]) +=
            join(Map(a(0) -> 1), Map(a(1) -> 1))

      val names = termDefs.keys.toList

      // fixed-point computation, to determine all products represented
      // by the individual terms

      var changed = true
      while (changed) {
        changed = false

        for (name <- names) {
          val products = termDefs(name)

          val newProducts =
            for (product <- products.iterator;
                 (t, mult) <- product.iterator;
                 if ((name != t) && (termDefs contains t));
                 tProduct <- termDefs(t).iterator)
            yield join(if (mult == 1)
                         product - t
                       else
                         product + (t -> (mult - 1)),
                       tProduct)

          val allProducts = products ++ newProducts
          if (products.size != allProducts.size) {
            changed = true
            termDefs.put(name, allProducts)
          }
        }
      }

//      println(termDefs.toList)

      // invert the termDefs mapping

      val productNames = new MHashMap[TermMultiset, MHashSet[Term]]
      for ((name, products) <- termDefs.iterator;
           product <- products.iterator)
        productNames.getOrElseUpdate(product, new MHashSet[Term]) += name

      // generate equations between different names representing the same
      // product

      import TerForConvenience._
      implicit val _ = goal.order

      val eqs =
        conj(for ((_, names) <- productNames.iterator;
                  Seq(name1, name2) <- names.iterator sliding 2)
             yield (name1 === name2))

//      println(eqs)

      if (eqs.isTrue)
        None
      else
        Some((eqs, Conjunction.TRUE))
    }
  })

  TheoryRegistry register this
}

////////////////////////////////////////////////////////////////////////////////

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._
  import MulTheory.mul

  val a = createConstant("a")
  val b = createConstant("b")
  val c = createConstant("c")

  scope {
    !! (mul(a, b) >= c)
    !! (mul(b, a) < c)
    println(???)
  }

  scope {
    !! (mul(a, b) >= c)
    !! (mul(b, a) <= c)
    println(???)
    println(partialModel)
  }

  scope {
    !! (mul(a, mul(b, b)) >= c)
    !! (mul(b, mul(a, b)) < c)
    println(???)
  }

  scope {
    !! (c === mul(a, b))
    !! (mul(a, c) >= 0)
    !! (mul(b, mul(a, a)) < 0)
    println(???)
  }

}