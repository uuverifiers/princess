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
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.parameters.{PreprocessingSettings, Param}
import ap.proof.theoryPlugins.Plugin
import ap.util.Debug

import scala.collection.mutable.{HashMap => MHashMap}

object Theory {

  private val AC = Debug.AC_THEORY

  def genAxioms(theoryFunctions : Seq[IFunction] = List(),
                theoryAxioms : IFormula = IExpression.i(true),
                genTotalityAxioms : Boolean = false,
                order : TermOrder = TermOrder.EMPTY,
                functionEnc : FunctionEncoder =
                  new FunctionEncoder(true, false))
              : (Seq[Predicate],
                 Formula,
                 TermOrder,
                 Map[IFunction, IExpression.Predicate]) = {
    import IExpression._

    var currentOrder = order
    for (f <- theoryFunctions) {
      val (_, o) =
        functionEnc(eqZero(IFunApp(f, for (_ <- 0 until f.arity) yield i(0))),
                    currentOrder)
      currentOrder = o
    }

    val sig = Signature(Set(), Set(),
                        currentOrder.orderedConstants, currentOrder)
    val preprocSettings = PreprocessingSettings.DEFAULT
    val (fors, _, sig3) =
      Preprocessing(INamedPart(PartName.NO_NAME, ~theoryAxioms),
                    List(), sig, preprocSettings, functionEnc)

    val newOrder = sig3.order
    val formula = 
      !ReduceWithConjunction(Conjunction.TRUE, newOrder)(
         Conjunction.conj(InputAbsy2Internal(
           IExpression.or(for (INamedPart(_, f) <- fors.iterator) yield f),
           newOrder), newOrder))

    val functionTranslation =
      (for ((p, f) <- functionEnc.predTranslation.iterator) yield (f, p)).toMap
    val funPredicates =
      theoryFunctions map functionTranslation

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, funPredicates == (newOrder sortPreds funPredicates))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    (funPredicates, formula, newOrder, functionTranslation)
  }

  /**
   * Apply preprocessing to a formula over some set of
   * theories, prior to sending the formula to a prover.
   */
  def preprocess(f : Conjunction,
                 theories : Seq[Theory],
                 order : TermOrder) : Conjunction =
//  ap.util.Timer.measure("theory preprocessing") {
    (f /: theories) { case (f, t) => t.preprocess(f, order) }
//  }

  //////////////////////////////////////////////////////////////////////////////

  trait Decoder[A] {
    def apply(d : IdealInt)(implicit ctxt : DecoderContext) : A
  }

  trait TheoryDecoderData

  trait DecoderContext {
    def getDataFor(t : Theory) : TheoryDecoderData
  }

  class DefaultDecoderContext(model : Conjunction) extends DecoderContext {
    private val decoderDataCache = new MHashMap[Theory, TheoryDecoderData]
    def getDataFor(t : Theory) : TheoryDecoderData =
      decoderDataCache.getOrElseUpdate(t, {
        (t generateDecoderData model).get
      })
  }

  //////////////////////////////////////////////////////////////////////////////

  object SatSoundnessConfig extends Enumeration {
    /**
     * Apart from symbols defined in the theories, only
     * constants exist in a problem. All quantifiers are
     * existential (in the antecedent).
     */
    val Elementary = Value
    /**
     * In addition to symbols defined in the theories, also
     * constants, uninterpreted predicates, and uninterpreted
     * functions can exist. Uninterpreted predicates
     * or uninterpreted partial functions can be defined through
     * e-matching.
     * All other quantifiers are existential (in the antecedent),
     * and in particular there are no function totality axioms.
     */
    val Existential = Value
    /**
     * In addition to symbols defined in the theories, also
     * constants, uninterpreted predicates, uninterpreted
     * functions, and arbitrary quantifiers can exist.
     */
    val General = Value
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * trait for representing signature and axioms of theories, e.g.,
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
   * A list of functions that should be considered in automatic trigger
   * generation
   */
  val triggerRelevantFunctions : Set[IFunction]

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
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */
  def preprocess(f : Conjunction,
                 order : TermOrder) : Conjunction = f

  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  def generateDecoderData(model : Conjunction)
                         : Option[Theory.TheoryDecoderData] =
    None

  /**
   * Check whether we can tell that the given combination of theories is
   * sound for checking satisfiability of a problem, i.e., if proof construction
   * ends up in a dead end, can it be concluded that a problem is satisfiable.
   */
  def isSoundForSat(theories : Seq[Theory],
                    config : Theory.SatSoundnessConfig.Value) : Boolean = false

}