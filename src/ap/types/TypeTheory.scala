/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2022 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.theories.Theory
import ap.parser.{ITerm, SizeVisitor}
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions,
                               ReduceWithConjunction}
import ap.terfor.preds.Atom
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer,
                                 HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashMap, LinkedHashSet}

/**
 * Theory taking care of types of declared symbols.
 */
object TypeTheory extends Theory {

  private val AC = Debug.AC_TYPES

  override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
    implicit val o = order

    val membershipConstraints =
      for (c <- f.constants.iterator;
           if c.isInstanceOf[SortedConstantTerm])
      yield (c.asInstanceOf[SortedConstantTerm].sort membershipConstraint c)

    val fWithFunctionConstraints = addResultConstraints(f, false)

    val res =
      if (membershipConstraints.hasNext)
        Conjunction.conj(membershipConstraints, order) ==>
          fWithFunctionConstraints
      else
        fWithFunctionConstraints

    ReduceWithConjunction(Conjunction.TRUE, order)(res)
  }

  override def postprocess(f : Conjunction,
                           order : TermOrder) : Conjunction =
    filterTypeConstraints(f)

  /**
   * Add constraints about implicitly existentially quantified constants.
   */
  def addExConstraints(f : Conjunction,
                       exConstants : Set[ConstantTerm],
                       order : TermOrder) : Conjunction = {
    implicit val o = order

    val membershipConstraints =
      for (c <- f.constants.iterator;
           if c.isInstanceOf[SortedConstantTerm] && (exConstants contains c))
      yield (c.asInstanceOf[SortedConstantTerm].sort membershipConstraint c)

    if (membershipConstraints.hasNext)
      Conjunction.conj((Iterator single f) ++ membershipConstraints, order)
    else
      f
  }

  /**
   * Remove redundant type constraints that might occur in the formula
   * (constraints that are implied by the typing information)
   */
  def filterTypeConstraints(f : Conjunction) : Conjunction = {
    implicit val order = f.order

    val membershipConstraints =
      for (c <- f.constants.iterator; if c.isInstanceOf[SortedConstantTerm])
      yield (c.asInstanceOf[SortedConstantTerm].sort membershipConstraint c)

    if (membershipConstraints.hasNext) {
      val membershipConstraintConj =
        Conjunction.conj(membershipConstraints, order)
      ReduceWithConjunction(membershipConstraintConj, order)(f)
    } else {
      f
    }
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

  override def toString = "Types"

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

  case class DecoderData(
               valueTranslation : scala.collection.Map[(IdealInt, Sort), ITerm])
     extends Theory.TheoryDecoderData

  override def generateDecoderData(model : Conjunction)
                                  : Option[Theory.TheoryDecoderData] = {
    val assignment = new LinkedHashMap[(IdealInt, Sort), ITerm]

    // find all relevant sorts and indexes
    val sorts = new LinkedHashSet[Sort]
    val allTerms = new LinkedHashSet[(IdealInt, Sort)]

    for (c <- model.constants)
      sorts += Sort sortOf c

    for (a <- atoms(model))
      sorts ++= SortedPredicate argumentSorts a

    // for models, we have to make sure that we construct symbolic expressions
    // for all relevant index-sort pairs

    for (lc <- model.arithConj.positiveEqs)
      if (lc.constants.size == 1) {
        val sort =
          SortedConstantTerm sortOf lc.leadingTerm.asInstanceOf[ConstantTerm]
        allTerms += ((-lc.constant, sort))
      }

    for (a <- model.predConj.positiveLits.iterator ++
              model.predConj.negativeLits.iterator;
         argSorts = SortedPredicate.argumentSorts(a.pred, a);
         (lc, sort) <- a.iterator zip argSorts.iterator;
         if lc.isConstant) {
      allTerms += ((lc.constant, sort))
    }

    val allTermsSet = allTerms.toSet

    // reconstruct terms from definitions in the model

    val definedIndexes = new MHashSet[(IdealInt, Sort)]

    var size = -1
    while (assignment.size > size) {
      size = assignment.size
      for (s <- sorts)
        s.augmentModelTermSet(model, assignment, allTermsSet, definedIndexes)

      if (size == assignment.size) {
        // possibly add further terms to the map, for sorted constants
        // that are mentioned but not further defined in the model

        val missing =
          for (p@(n, sort) <- allTerms.iterator;
               if sort.decodeToTerm(n, assignment).isEmpty &&
                  !(definedIndexes contains p))
          yield p

        if (missing.hasNext) {
          val usedTerms =
            (for ((n, sort) <- allTerms.iterator;
                  t <- sort.decodeToTerm(n, assignment).iterator)
             yield (sort, t)).toSet
          val witnesses =
            for (p@(ind, sort) <- missing) yield {
              val witness = (sort.individuals.iterator filterNot {
                               t => usedTerms contains (sort, t) }).next
              (p, witness)
            }

          // as a convention, we always add a term of minimum size that is
          // not currently used. Some theories, for instance ADTs depend
          // on the fact that the smallest term is used

          val (key, t) =
            witnesses minBy { case (_, t) => SizeVisitor(t) }
          assignment.put(key, t)
        }
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // all terms have been assigned
    Debug.assertPost(AC,
      allTerms forall { case (n, sort) => {
                         val res = sort.decodeToTerm(n, assignment).isDefined
                          if (!res)
                            throw new Exception(
                              "value " + (n, sort) +
                                " could not be reconstructed; this is probably"+
                                " a bug in one of the used theories")
                         res
                        } })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    Some(DecoderData(assignment))
  }

  private def atoms(c : Conjunction) : Iterator[Atom] =
    c.predConj.positiveLits.iterator ++
    c.predConj.negativeLits.iterator ++
    (for (d <- c.negatedConjs.iterator; a <- atoms(d)) yield a)

}
