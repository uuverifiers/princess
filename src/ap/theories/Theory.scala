/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2014 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.parameters.{PreprocessingSettings, Param}
import ap.proof.theoryPlugins.Plugin

object Theory {

  def toInternal(axioms : IFormula,
                 genTotalityAxioms : Boolean,
                 order : TermOrder)
              : (Formula,
                 TermOrder,
                 Map[IFunction, IExpression.Predicate]) =
    toInternal(axioms,
               genTotalityAxioms,
               order,
               new FunctionEncoder(true, false, Map()))

  def toInternal(axioms : IFormula,
                 genTotalityAxioms : Boolean,
                 order : TermOrder,
                 functionEnc : FunctionEncoder)
              : (Formula,
                 TermOrder,
                 Map[IFunction, IExpression.Predicate]) = {
    val sig = Signature(Set(), Set(), order.orderedConstants, order)
    val preprocSettings = PreprocessingSettings.DEFAULT
    val (fors, _, newSig) =
      Preprocessing(INamedPart(PartName.NO_NAME, ~axioms),
                    List(), sig, preprocSettings, functionEnc)

    val newOrder = newSig.order

    val formula = 
      !ReduceWithConjunction(Conjunction.TRUE, newOrder)(
         Conjunction.conj(InputAbsy2Internal(
           IExpression.or(for (INamedPart(_, f) <- fors.iterator) yield f),
           newOrder), newOrder))

    val functionTranslation =
      (for ((p, f) <- functionEnc.predTranslation.iterator) yield (f, p)).toMap

    (formula, newOrder, functionTranslation)
  }

  //////////////////////////////////////////////////////////////////////////////

  trait Decoder[A] {
    def apply(d : IdealInt)(implicit ctxt : DecoderContext) : A
  }

  trait TheoryDecoderData

  trait DecoderContext {
    def getDataFor(t : Theory) : TheoryDecoderData
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Trait for representing signature and axioms of theories, e.g.,
 * the theory of arrays. This is used to make sure that theory symbols are
 * unique.
 */
trait Theory {

  /**
   * Interpreted functions of the theory
   */
  val functions  : Seq[IFunction]

  /**
   * Interpreted predicates of the theory
   */
  val predicates : Seq[IExpression.Predicate]

  /**
   * Add the symbols defined by this theory to the <code>order</code>
   */
  def extend(order : TermOrder) : TermOrder =
    order extendPred predicates

  /**
   * Mapping of interpreted functions to interpreted predicates, used
   * translating input ASTs to internal ASTs (the latter only containing
   * predicates).
   */
  val functionPredicateMapping : Seq[(IFunction, IExpression.Predicate)]

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates : Set[IExpression.Predicate]

  /**
   * Information how interpreted predicates should be handled for
   * e-matching.
   */
  val predicateMatchConfig : Signature.PredicateMatchConfig

  /**
   * When instantiating existentially quantifier formulas,
   * <code>EX phi</code>, at most one instantiation is necessary
   * provided that all predicates in <code>phi</code> are contained
   * in this set.
   */
  val singleInstantiationPredicates : Set[IExpression.Predicate] = Set()

  /**
   * Axioms defining the theory; such axioms are simply added as formulae
   * to the problem to be proven, and thus handled using the standard
   * reasoning techniques (including e-matching).
   */
  val axioms : Formula

  /**
   * Additional axioms that are included if the option
   * <code>+genTotalityAxioms</code> is given to Princess.
   */
  val totalityAxioms : Formula

  /**
   * Optionally, a plug-in implementing reasoning in this theory
   */
  def plugin : Option[Plugin]

  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  def generateDecoderData(model : Conjunction)
                         : Option[Theory.TheoryDecoderData] =
    None

}
