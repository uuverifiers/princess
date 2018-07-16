/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.strings

import ap.Signature
import ap.parser.{IFunction, ITerm}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ADT, ModuloArithmetic, TheoryRegistry}
import ap.types.Sort
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.{HashMap => MHashMap}

object SeqStringTheory {

  private val instances = new MHashMap[Int, SeqStringTheory]

  def apply(bitWidth : Int) : SeqStringTheory = synchronized {
    instances.getOrElseUpdate(bitWidth, new SeqStringTheory(bitWidth))
  }

}

/**
 * Generic class describing string theories.
 */
class SeqStringTheory private (val bitWidth : Int) extends {

  val CharSort = ModuloArithmetic.UnsignedBVSort(bitWidth)
  val RegexSort = new Sort.InfUninterpreted("RegLan")

  val seqADT =
    new ADT (List("String"),
             List(("str_empty", ADT.CtorSignature(List(), ADT.ADTSort(0))),
                  ("str_cons",  ADT.CtorSignature(
                                  List(("str_head", ADT.OtherSort(CharSort)),
                                       ("str_tail", ADT.ADTSort(0))),
                                ADT.ADTSort(0)))),
             measure = ADT.TermMeasure.Size)

  val StringSort = seqADT.sorts.head

} with AbstractStringTheory {

  val Seq(str_empty, str_cons) =        seqADT.constructors
  val Seq(_, Seq(str_head, str_tail)) = seqADT.selectors

  def int2Char(t : ITerm) : ITerm =
    ModuloArithmetic.cast2UnsignedBV(bitWidth, t)

  def char2Int(t : ITerm) : ITerm = t

  val transducers : Map[String, Predicate] = Map()
  
  //////////////////////////////////////////////////////////////////////////////

  val functions = predefFunctions
  
  val (funPredicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions)

  val predicates = predefPredicates ++ funPredicates

  val functionPredicateMapping = functions zip funPredicates
  val functionalPredicates = funPredicates.toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  override val dependencies : Iterable[Theory] = List(seqADT, ModuloArithmetic)

  def plugin = None

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}