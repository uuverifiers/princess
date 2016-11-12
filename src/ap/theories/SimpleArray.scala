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

package ap.theories

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom

import scala.collection.mutable.{HashMap => MHashMap}

object SimpleArray {
  
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
           Theory.SatSoundnessConfig.Existential =>
        theories forall {
          t => t.isInstanceOf[SimpleArray] ||
               t == BitShiftMultiplication ||
               t == nia.GroebnerMultiplication
        }
      case Theory.SatSoundnessConfig.General =>
        false
    }

  //////////////////////////////////////////////////////////////////////////////

  case class DecoderData(selectAtoms : Seq[Atom])
       extends Theory.TheoryDecoderData

  val asMap = new Theory.Decoder[Map[Seq[IdealInt], IdealInt]] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext)
             : Map[Seq[IdealInt], IdealInt] =
      (ctxt getDataFor SimpleArray.this) match {
        case DecoderData(atoms) =>
          (for (a <- atoms.iterator; if (a(0).constant == d))
           yield (for (lc <- a.slice(1, a.size - 1)) yield lc.constant,
                  a.last.constant)).toMap
      }
  }

  override def generateDecoderData(model : Conjunction)
                                  : Option[Theory.TheoryDecoderData] =
    Some(DecoderData(model.predConj positiveLitsWithPred predicates(0)))

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = "SimpleArray(" + arity + ")"

}
