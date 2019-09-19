/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2019 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.theories.{Theory, TheoryRegistry}
import ap.parser._
import ap.terfor.{TermOrder, Term, Formula, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.linearcombination.LinearCombination

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet, HashMap => MHashMap}

import ap.util.Debug

object UninterpretedSortTheory {

  /**
   * Create a new uninterpreted sort of infinite cardinality.
   */
  def createInfUninterpretedSort(name : String) : InfUninterpretedSort =
    new InfUninterpretedSort(name)

  /**
   * Create a new uninterpreted sort of finite or infinite cardinality.
   */
  def createUninterpretedSort(name : String) : UninterpretedSort =
    (new UninterpretedSortTheory (name)).sort

  /**
   * Extractor to identify predicates that are domain predicates of some sort.
   */
  object DomainPredicate {
    def unapply(p : Predicate) : Option[Sort] =
      for (t <- lookupDomainPredicate(p)) yield t.sort
  }

  //////////////////////////////////////////////////////////////////////////////

  class UninterpretedSort protected[types]
                         (val name : String,
                          val theory : UninterpretedSortTheory) extends Sort {

    def membershipConstraint(t : ITerm) : IFormula =
      IAtom(theory.domainPredicate, List(t))

    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
      Atom(theory.domainPredicate, List(LinearCombination(t, order)), order)

    val cardinality : Option[IdealInt] = None
    
    /**
     * We just create numbered constants to represent the individuals.
     */
    override val individuals : Stream[ITerm] =
      for (n <- Stream.iterate(0)(_ + 1))
      yield IConstant(newConstant(name + "!" + n))

    def augmentModelTermSet(model : Conjunction,
                            assignment : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {}
    
    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      val ind = d.intValueSafe
      if (ind >= 0)
        Some(individuals(2*ind))
      else
        Some(individuals(-2*ind - 1))
    }

  }

  class InfUninterpretedSort protected[types] (override val name : String)
        extends ProxySort(Sort.Integer) {

    /**
     * We just create numbered constants to represent the individuals.
     */
    override val individuals : Stream[ITerm] =
      for (n <- Stream.iterate(0)(_ + 1))
      yield IConstant(newConstant(name + "!" + n))

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      val ind = d.intValueSafe
      if (ind >= 0)
        Some(individuals(2*ind))
      else
        Some(individuals(-2*ind - 1))
    }
  }

  def lookupDomainPredicate(p : Predicate) : Option[UninterpretedSortTheory] =
    (TheoryRegistry lookupSymbol p) match {
      case Some(t : UninterpretedSortTheory) => Some(t)
      case _ => None
    }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Theory to handle an uninterpreted sort. To ensure correct semantics,
 * (non-empty, but cardinality might be finite or infinite), each
 * uninterpreted sort is associated to a domain predicate, and an axiom
 * specifying inhabitation is added.
 */
class UninterpretedSortTheory(name : String) extends Theory {

  import UninterpretedSortTheory._

  private val AC = Debug.AC_TYPES

  override def toString = "Sort(" + name + ")"

  val sort = new UninterpretedSort(name, this)

  val domainPredicate = new Predicate(name, 1)

  val functionPredicateMapping = List()
  val functionalPredicates : Set[ap.parser.IExpression.Predicate] = Set()
  val functions = List()
  def plugin = None
  val predicates = List(domainPredicate)
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[ap.parser.IFunction] = Set()

  val predicateMatchConfig : ap.Signature.PredicateMatchConfig =
    Map(domainPredicate -> ap.Signature.PredicateMatchStatus.None)

  private implicit val order = TermOrder.EMPTY.extendPred(domainPredicate)

  import TerForConvenience._

  val axioms = exists(domainPredicate(List(l(v(0)))))

  override def isSoundForSat(
         theories : Seq[Theory],
         config : Theory.SatSoundnessConfig.Value) : Boolean =
    Set(Theory.SatSoundnessConfig.Elementary,
        Theory.SatSoundnessConfig.Existential) contains config

  TheoryRegistry register this

}

