/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2019-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.types

import ap.Signature
import ap.basetypes.IdealInt
import ap.theories.{Theory, TheoryRegistry}
import ap.parser._
import ap.terfor.{TermOrder, Term, Formula, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.linearcombination.LinearCombination

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet, HashMap => MHashMap,
                                 ArrayBuffer}

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
                          val theory : UninterpretedSortTheory)
        extends Theory.TheorySort {

    def membershipConstraint(t : ITerm) : IFormula =
      IAtom(theory.domainPredicate, List(t))

    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
      Atom(theory.domainPredicate, List(LinearCombination(t, order)), order)

    val cardinality : Option[IdealInt] = None

    private val individualHandler = new IndividualHandler(this)

    /**
     * We just create numbered constants to represent the individuals.
     */
    override val individuals : Stream[ITerm] = individualHandler.individuals

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(individualHandler(d))

    def augmentModelTermSet(model : Conjunction,
                            assignment : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {}
  }

  class InfUninterpretedSort protected[types] (override val name : String)
        extends ProxySort(Sort.Integer) {

    private val individualHandler = new IndividualHandler(this)

    /**
     * We just create numbered constants to represent the individuals.
     */
    override val individuals : Stream[ITerm] = individualHandler.individuals

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(individualHandler(d))
  }

  //////////////////////////////////////////////////////////////////////////////

  private class IndividualHandler(sort : Sort) {

    private val individualMap = new MHashMap[IdealInt, ITerm]

    def apply(d : IdealInt) : ITerm = synchronized {
      individualMap.getOrElseUpdate(d, {
        val name = if (d.signum >= 0)
                     sort.name + "!" + (2*d)
                   else
                     sort.name + "!" + (-2*d - 1)
        IConstant(sort newConstant name)
      })
    }

    val individuals : Stream[ITerm] =
      for (n <- Stream.iterate(IdealInt.ZERO){
             n => if (n.signum >= 0) (-n-1) else -n
           })
      yield apply(n)

  }

  //////////////////////////////////////////////////////////////////////////////

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

  val domainPredicate = MonoSortedPredicate(name, List(sort))

  val functionPredicateMapping = List()
  val functionalPredicates : Set[ap.parser.IExpression.Predicate] = Set()
  val functions = List()
  def plugin = None
  val predicates = List(domainPredicate)
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[ap.parser.IFunction] = Set()

  val predicateMatchConfig : ap.Signature.PredicateMatchConfig =
    Map(domainPredicate -> ap.Signature.PredicateMatchStatus.None)

  private implicit val order : TermOrder =
    TermOrder.EMPTY.extendPred(domainPredicate)

  import TerForConvenience._

  val axioms = exists(domainPredicate(List(l(v(0)))))

  /**
   * In the post-processing we eliminate domain predicates again, and
   * if necessary add types of quantifiers.
   */
  override def iPostprocess(f : IFormula, signature : Signature) : IFormula = {
    val visitor = new DomainPredicateEliminator
    visitor.visit(f, ()).asInstanceOf[IFormula]
  }

  private class DomainPredicateEliminator
          extends CollectingVisitor[Unit, IExpression] {
    private val variableSorts = new ArrayBuffer[Sort]

    private def popVariableSort : Sort = {
      val res = variableSorts.last
      variableSorts reduceToSize (variableSorts.size - 1)
      res
    }

    override def preVisit(t : IExpression,
                          ctxt : Unit) : PreVisitResult = t match {
      case t : IVariableBinder => {
        variableSorts += t.sort
        KeepArg
      }
      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression,
                  ctxt : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`domainPredicate`, _) =>
        subres match {
          case Seq(IVariable(ind)) => {
            val pos = variableSorts.size - ind - 1
            if (pos >= 0) {
              val oldSort = variableSorts(pos)
              if (oldSort != Sort.AnySort && oldSort != sort)
                Console.err.println(
                  "Warning: inconsistent sorts " + oldSort + " and " + sort +
                    " of quantified variable")
              variableSorts(pos) = sort
            }
            IBoolLit(true)
          }
          case Seq(t : ITerm) => {
            val oldSort = Sort sortOf t
            if (oldSort != sort)
              Console.err.println(
                "Warning: inconsistent sorts " + oldSort + " and " + sort +
                  " of term " + t)
            IBoolLit(true)
          }
        }

      case ISortedQuantified(q, qSort, _) =>
        popVariableSort match {
          case `qSort` =>
            t update subres
          case newSort => {
            val newBody =
              VariableSubstVisitor(subres.head.asInstanceOf[IFormula],
                                   (List(ISortedVariable(0, newSort)), 0))
            ISortedQuantified(q, newSort, newBody)
          }
        }

      case ISortedEpsilon(eSort, _) =>
        popVariableSort match {
          case `eSort` =>
            t update subres
          case newSort => {
            val newBody =
              VariableSubstVisitor(subres.head.asInstanceOf[IFormula],
                                   (List(ISortedVariable(0, newSort)), 0))
            ISortedEpsilon(newSort, newBody)
          }
        }

      case _ =>
        t update subres
    }
  }

  override def isSoundForSat(
         theories : Seq[Theory],
         config : Theory.SatSoundnessConfig.Value) : Boolean =
    Set(Theory.SatSoundnessConfig.Elementary,
        Theory.SatSoundnessConfig.Existential) contains config

  TheoryRegistry register this

}

