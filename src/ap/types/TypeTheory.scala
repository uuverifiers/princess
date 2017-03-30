/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.types

import ap.basetypes.IdealInt
import ap.theories.Theory
import ap.parser.ITerm
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}

import scala.collection.mutable.{ArrayBuffer,
                                 HashMap => MHashMap, HashSet => MHashSet}

/**
 * Theory taking care of types of declared symbols.
 */
object TypeTheory extends Theory {

  override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
    implicit val _ = order

    val membershipConstraints =
      for (c <- f.constants.iterator;
           if c.isInstanceOf[SortedConstantTerm])
      yield (c.asInstanceOf[SortedConstantTerm].sort membershipConstraint c)

    val fWithFunctionConstraints = addResultConstraints(f, false)

    if (membershipConstraints.hasNext)
      Conjunction.conj(membershipConstraints, order) ==>
        fWithFunctionConstraints
    else
      fWithFunctionConstraints
  }

  /**
   * Add constraints about implicitly existentially quantified constants.
   */
  def addExConstraints(f : Conjunction,
                       exConstants : Set[ConstantTerm],
                       order : TermOrder) : Conjunction = {
    implicit val _ = order

    val membershipConstraints =
      for (c <- f.constants.iterator;
           if c.isInstanceOf[SortedConstantTerm] && (exConstants contains c))
      yield (c.asInstanceOf[SortedConstantTerm].sort membershipConstraint c)

    if (membershipConstraints.hasNext)
      Conjunction.conj((Iterator single f) ++ membershipConstraints, order)
    else
      f
  }

  private def addResultConstraints(f : Conjunction, negated : Boolean)
                                  (implicit order : TermOrder) : Conjunction = {
    val newNegConj =
      f.negatedConjs.update(for (c <- f.negatedConjs)
                              yield addResultConstraints(c, !negated),
                            order)
    if (negated) {

      val newConjuncts = new ArrayBuffer[Formula]

      for (a <- f.predConj.positiveLits) a.pred match {
        case p : SortedPredicate =>
          newConjuncts += p sortConstraints a
        case _ =>
          // nothing
      }

      val updatedF = f updateNegatedConjs newNegConj

      if (newConjuncts.isEmpty) {
        updatedF
      } else if (updatedF.quans.isEmpty) {
        newConjuncts += updatedF
        Conjunction.conj(newConjuncts, order)
      } else {
        newConjuncts += updatedF unquantify updatedF.quans.size
        val matrix = Conjunction.conj(newConjuncts, order)
        Conjunction.quantify(updatedF.quans, matrix, order)
      }

    } else { // !negated

      val newDisjuncts = new ArrayBuffer[Conjunction]

      val newNegLits = f.predConj.negativeLits filter { a =>
        a.pred match {
          case p : SortedPredicate => {
            val constr = p sortConstraints a
            if (constr.isTrue) {
              // just keep this literal
              true
            } else {
              newDisjuncts += Conjunction.conj(List(a, constr), order)
              false
            }
          }
          case _ =>
            // keep this literal
            true
        }
      }

      if (newDisjuncts.isEmpty) {
        f updateNegatedConjs newNegConj
      } else {
        val newPredConj =
          f.predConj.updateLits(f.predConj.positiveLits, newNegLits)
        val finalNegConj =
          NegatedConjunctions(newNegConj ++ newDisjuncts, order)
        Conjunction(f.quans, f.arithConj, newPredConj, finalNegConj, order)
      }
    }
  }

  override def isSoundForSat(
         theories : Seq[Theory],
         config : Theory.SatSoundnessConfig.Value) : Boolean = true

  //////////////////////////////////////////////////////////////////////////////

  val axioms = Conjunction.TRUE
  val functionPredicateMapping = List()
  val functionalPredicates : Set[ap.parser.IExpression.Predicate] = Set()
  val functions = List()
  def plugin = None
  val predicateMatchConfig : ap.Signature.PredicateMatchConfig = Map()
  val predicates = List()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[ap.parser.IFunction] = Set()

  //////////////////////////////////////////////////////////////////////////////

  case class DecoderData(valueTranslation : Map[(IdealInt, Sort), ITerm])
     extends Theory.TheoryDecoderData

  override def generateDecoderData(model : Conjunction)
                                  : Option[Theory.TheoryDecoderData] = {
    // find all relevant sorts
    val sorts = new MHashSet[Sort]

    for (c <- model.constants) c match {
      case c : SortedConstantTerm =>
        sorts += c.sort
      case _ =>
        // nothing
    }

    for (a <- model.groundAtoms) a.pred match {
      case sortedPred : SortedPredicate =>
        sorts ++= sortedPred argumentTypes a
      case _ =>
        // nothing
    }

    val terms = new MHashMap[(IdealInt, Sort), ITerm]

    var size = -1
    while (terms.size > size) {
      size = terms.size
      for (s <- sorts)
        s.augmentModelTermSet(model, terms)
    }

    Some(DecoderData(terms.toMap))
  }

}