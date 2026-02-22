/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2024 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.theories.arrays

import ap.theories._
import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.types.{TypeTheory, ProxySort, MonoSortedIFunction}
import ap.interpolants.ArraySimplifier

import scala.collection.mutable.{HashMap => MHashMap}

object SimpleArray {

  import IExpression.Sort
  
  private val instances = new MHashMap[Int, SimpleArray]

  def apply(arity : Int) : SimpleArray = synchronized {
    instances.getOrElseUpdate(arity, new SimpleArray(arity))
  }

  /**
   * Extractor recognising the <code>select</code> function of
   * any array theory.
   */
  object Select {
    def unapply(fun : IFunction) : Boolean =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : SimpleArray) => fun == t.select
        case _ => false
      }
  }

  /**
   * Extractor recognising the <code>store</code> function of
   * any array theory.
   */
  object Store {
    def unapply(fun : IFunction) : Boolean =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : SimpleArray) => fun == t.store
        case _ => false
      }
  }

  /**
   * Sort representing arrays. At the moment the sorts only distinguish
   * the arity of arrays, not the index and element sorts.
   */
  case class ArraySort(arity : Int) extends ProxySort(Sort.Integer) {
    override val name : String =
      "SimpleArray" + (if (arity == 1) "" else "_" + arity)
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

  val sort = new SimpleArray.ArraySort(arity)

  val select =
    MonoSortedIFunction(
      prefix + "select" + suffix,
      List(sort) ++ (for (_ <- 0 until arity) yield Sort.Integer),
      Sort.Integer,
      partial, false)
  val store =
    MonoSortedIFunction(
      prefix + "store" + suffix,
      List(sort) ++ (for (_ <- 0 to arity) yield Sort.Integer),
      sort,
      partial, false)
  
  val functions = List(select, store)

  val (predicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms =
                       Parser2InputAbsy.arrayAxioms(arity, select, store))

  val functionPredicateMapping = functions zip predicates
  val totalityAxioms = Conjunction.TRUE

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val triggerRelevantFunctions : Set[IFunction] = functions.toSet

  val functionalPredicates = predicates.toSet

  val plugin = None

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary |
           Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Map from array indices to arrays represented as maps
   */
  case class DecoderData(
               arrayMaps : Map[IdealInt, Map[Seq[IdealInt], IdealInt]])
       extends Theory.TheoryDecoderData

  val asMap = new Theory.Decoder[Map[Seq[IdealInt], IdealInt]] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext)
             : Map[Seq[IdealInt], IdealInt] =
      (ctxt getDataFor SimpleArray.this) match {
        case DecoderData(map) => map.getOrElse(d, Map())
      }
  }

  override def generateDecoderData(model : Conjunction)
                                  : Option[Theory.TheoryDecoderData] = {
    val arrays = new MHashMap[IdealInt, MHashMap[Seq[IdealInt], IdealInt]]

    // extract select literals
    for (a <- model.predConj positiveLitsWithPred predicates(0)) {
      val arIndex =
        a(0).constant
      val arMap =
        arrays.getOrElseUpdate(arIndex, new MHashMap[Seq[IdealInt], IdealInt])
      arMap.put(for (lc <- a.slice(1, a.size - 1)) yield lc.constant,
                a.last.constant)
    }

    // extract store literals, propagate maps
    var changed = true
    while (changed) {
      changed = false
      
      for (a <- model.predConj positiveLitsWithPred predicates(1)) {
        val fromIndex = a(0).constant
        val toIndex = a.last.constant

        val fromMap = arrays.getOrElseUpdate(fromIndex,
                                       new MHashMap[Seq[IdealInt], IdealInt])
        val toMap = arrays.getOrElseUpdate(toIndex,
                                       new MHashMap[Seq[IdealInt], IdealInt])

        for ((key, value) <- fromMap)
          if (!(toMap contains key)) {
            toMap.put(key, value)
            changed = true
          }
      }
    }

    Some(DecoderData(
      (for ((ind, map) <- arrays.iterator) yield (ind, map.toMap)).toMap))
  }

  //////////////////////////////////////////////////////////////////////////////

  private val simp = new ArraySimplifier

  override val postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ simp.rewritings

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = "SimpleArray(" + arity + ")"

}
