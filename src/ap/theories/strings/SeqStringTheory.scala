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
import ap.parser._
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ADT, ModuloArithmetic, TheoryRegistry}
import ap.types.Sort
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.substitutions.VariableShiftSubst

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

  private val adtSize = seqADT.termSize.head
  private val adtSizePred = seqADT.termSizePreds.head

  /**
   * Visitor called during pre-processing to eliminate symbols
   * <code>str, str_len</code>
   */
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`str`, _) =>
        str_cons(subres.head.asInstanceOf[ITerm], str_empty())
      case IFunApp(`str_len`, _) =>
        adtSize(subres.head.asInstanceOf[ITerm])
      case t =>
        t update subres
    }
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) =
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  //////////////////////////////////////////////////////////////////////////////

  private object StringPred {
    val reverseMapping =
      (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap
    def unapply(p : Predicate) : Option[IFunction] = reverseMapping get p
  }

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    import TerForConvenience._

//    println("init: " + f)

    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case StringPred(`str_++`) if negated => {
          val shiftedA = VariableShiftSubst(0, 2, order)(a)
          exists(2, shiftedA &
                    adtSizePred(List(shiftedA(0), l(v(0)))) &
                    adtSizePred(List(shiftedA(1), l(v(1)))) &
                    adtSizePred(List(shiftedA(2), v(0) + v(1) - 1)))
        }
        case _ =>
          a
      }
    }

//    println("after1: " + after1)
    after1
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}
