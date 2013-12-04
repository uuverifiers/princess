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

package ap.theories

import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.{HashMap => MHashMap}

object SimpleArray {
  
  private val instances = new MHashMap[Int, SimpleArray]

  def apply(arity : Int) : SimpleArray = synchronized {
    instances.getOrElseUpdate(arity, new SimpleArray(arity))
  }

}

/**
 * Simple implementation of an array theory.
 */
class SimpleArray private (arity : Int) extends Theory {

  import IExpression._

  private val (prefix, suffix) =
    if (arity == 1) ("", "") else ("_", "_" + arity)

  private val partial = false

  val select = new IFunction(prefix + "select" + suffix, arity + 1, partial, false)
  val store = new IFunction(prefix + "store" + suffix, arity + 2, partial, false)
  
  val functions = List(select, store)

  val (predicates, axioms, totalityAxioms) = {
    val (axioms, _, functionTranslation) =
      Theory.toInternal(Parser2InputAbsy.arrayAxioms(arity, select, store),
                        false,
                        TermOrder.EMPTY)
    (List(functionTranslation(select), functionTranslation(store)),
     axioms,
     Conjunction.TRUE)
  }

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val functionalPredicates = predicates.toSet

  val functionPredicateMapping =
    List((select, predicates(0)), (store, predicates(1)))

  val plugin = None

  TheoryRegistry register this

}