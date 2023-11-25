/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.basetypes.IdealInt
import ap.{Signature, PresburgerTools}
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPluginFactory,
                               IdentityReducerPluginFactory}
import ap.terfor.substitutions.VariableShiftSubst
import ap.parameters.{PreprocessingSettings, Param}
import ap.proof.theoryPlugins.Plugin
import ap.types.Sort
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 LinkedHashSet}

object Theory {

  private val AC = Debug.AC_THEORY

  /**
   * Preprocess a set of axioms and convert them to internal representation.
   */
  def genAxioms(theoryFunctions : Seq[IFunction] = List(),
                theoryAxioms : IFormula          = IExpression.i(true),
                extraPredicates : Seq[Predicate] = List(),
                genTotalityAxioms : Boolean      = false,
                preOrder : TermOrder             = TermOrder.EMPTY,
                functionEnc : FunctionEncoder    = new FunctionEncoder(true,
                                                                       false),
                otherTheories : Seq[Theory]      = List())
             : (Seq[Predicate],
                Formula,
                TermOrder,
                Map[IFunction, IExpression.Predicate]) = {
    import IExpression._

    var currentOrder = preOrder extendPred extraPredicates

    val knownTheories = new LinkedHashSet[Theory]

    def addTheory(t : Theory) : Unit = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, t != this,
                      "When processing theory axioms, the theory itself must " +
                        "not be assumed as a known theory. This error might " +
                        "indicate cyclic dependencies among theories")
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      if (knownTheories add t) {
        for (s <- t.dependencies)
          addTheory(s)
        currentOrder = t extend currentOrder
        functionEnc addTheory t
      }
    }

    for (t <- otherTheories)
      addTheory(t)

    for (f <- theoryFunctions) {
      val (_, o) =
        functionEnc(eqZero(IFunApp(f, for (_ <- 0 until f.arity) yield i(0))),
                    currentOrder)
      currentOrder = o
    }

    val sig = Signature(Set(), Set(), currentOrder.orderedConstants,
                        Map(), currentOrder, knownTheories.toSeq)
    val preprocSettings = PreprocessingSettings.DEFAULT
    val (fors, _, newSig) =
      Preprocessing(INamedPart(PartName.NO_NAME, ~theoryAxioms),
                    List(), sig, preprocSettings, functionEnc)

    val newOrder = newSig.order
    val formula = 
      !Theory.preprocess(
        ReduceWithConjunction(Conjunction.TRUE, newOrder)(
           Conjunction.conj(InputAbsy2Internal(
             IExpression.or(for (INamedPart(_, f) <- fors.iterator) yield f),
             newOrder), newOrder)),
        newSig.theories, newOrder)

    val functionTranslation =
      (for ((p, f) <- functionEnc.predTranslation.iterator) yield (f, p)).toMap
    val funPredicates =
      theoryFunctions map functionTranslation

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, funPredicates == (newOrder sortPreds funPredicates))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    (extraPredicates ++ funPredicates, formula, newOrder, functionTranslation)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Apply preprocessing to a formula over some set of
   * theories, prior to sending the formula to a prover.
   * This method will be called form within <code>ap.parser.Preprocessing</code>
   */
  def iPreprocess(f : IFormula,
                  theories : Seq[Theory], signature : Signature)
                 : (IFormula, Signature) =
//  ap.util.Timer.measure("theory iPreprocessing") {
    (theories :\ (f, signature)) { case (t, (f, s)) => t.iPreprocess(f, s) }
//  }

  /**
   * Apply preprocessing to a formula over some set of
   * theories, prior to sending the formula to a prover.
   */
  def preprocess(f : Conjunction,
                 theories : Seq[Theory],
                 order : TermOrder) : Conjunction =
//  ap.util.Timer.measure("theory preprocessing") {
    (theories :\ f) { case (t, f) => t.preprocess(f, order) }
//  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Optionally, a post-processor that is applied to formulas output by the
   * prover, for instance to interpolants or the result of quantifier
   * elimination.
   * This method will be called form within
   * <code>ap.parser.Postprocessing</code>.
   */
  def iPostprocess(f : IFormula,
                  theories : Seq[Theory], signature : Signature)
                 : IFormula =
//  ap.util.Timer.measure("theory iPostprocessing") {
    (f /: theories) { case (f, t) => t.iPostprocess(f, signature) }
//  }

  /**
   * Optionally, a post-processor that is applied to formulas output by the
   * prover, for instance to interpolants or the result of quantifier
   * elimination.
   * This method will be called form within
   * <code>ap.parser.Postprocessing</code>.
   */
  def postprocess(f : Conjunction,
                  theories : Seq[Theory],
                  order : TermOrder) : Conjunction =
//  ap.util.Timer.measure("theory postprocessing") {
    (f /: theories) { case (f, t) => t.postprocess(f, order) }
//  }

  /**
   * Compute the list of simplifiers defined by the theories.
   */
  def postSimplifiers(theories : Seq[Theory]) : Seq[IExpression => IExpression]=
    for (t <- theories; s <- t.postSimplifiers) yield s

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Apply a uniform substitution to a formula, rewriting atoms to arbitrary
   * new formulas.
   * TODO: optimise
   */
  def rewritePreds(f : Conjunction, order : TermOrder)
                  (rewrite : (Atom, Boolean) => Formula) : Conjunction =
    rewritePredsHelp(f, false, order)(rewrite)

  def rewritePredsHelp(f : Conjunction, negated : Boolean, order : TermOrder)
                      (rewrite : (Atom, Boolean) => Formula) : Conjunction = {
    var newFors = List[Formula]()

    val newPosLits =
      (for (a <- f.predConj.positiveLits.iterator;
            newF = rewrite(a, negated);
            b <- newF match {
              case b : Atom =>
                Iterator single b
              case newF => {
                newFors = newF :: newFors
                Iterator.empty
              }
            })
       yield b).toArray

    val newNegLits =
      (for (a <- f.predConj.negativeLits.iterator;
            newF = rewrite(a, !negated);
            b <- newF match {
              case b : Atom =>
                Iterator single b
              case newF => {
                newFors = Conjunction.negate(newF, order) :: newFors
                Iterator.empty
              }
            })
       yield b).toArray

    val newPredConj = f.predConj.updateLits(newPosLits, newNegLits)(order)

    val newNegConjs =
      f.negatedConjs.update(
        for (c <- f.negatedConjs)
        yield rewritePredsHelp(c, !negated, order)(rewrite), order)

    if (newFors.isEmpty &&
        (newPredConj eq f.predConj) &&
        (newNegConjs eq f.negatedConjs)) {
      f
    } else if (newFors.isEmpty) {
      Conjunction(f.quans, f.arithConj, newPredConj, newNegConjs, order)
    } else {
      val quantifiedParts =
        PresburgerTools toPrenex Conjunction.conj(newFors, order)
      val newQuanNum =
        quantifiedParts.quans.size

      val unquantifiedParts =
        VariableShiftSubst(0, newQuanNum, order)(
          Conjunction(List(), f.arithConj, newPredConj, newNegConjs, order))

      Conjunction.quantify(
        quantifiedParts.quans ++ f.quans,
        Conjunction.conj(
          List(quantifiedParts unquantify newQuanNum, unquantifiedParts),
          order),
        order)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * In some theories, complex values will internally be encoded as integers.
   * Decoders are used to translate back to foreground objects.
   */
  trait Decoder[A] {
    def apply(d : IdealInt)(implicit ctxt : DecoderContext) : A
  }

  trait TheoryDecoderData

  trait DecoderContext {
    def getDataFor(t : Theory) : TheoryDecoderData
  }

  /**
   * Decoder context that will extract all data from the given
   * <code>model</code>.
   */
  class DefaultDecoderContext(model : Conjunction) extends DecoderContext {
    private val decoderDataCache = new MHashMap[Theory, TheoryDecoderData]
    def getDataFor(t : Theory) : TheoryDecoderData =
      decoderDataCache.getOrElseUpdate(t, {
        (t generateDecoderData model).get
      })
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Test whether <code>p</code> belongs to any set
   * <code>Theory.modelGenPredicates</code>.
   */
  def isModelGenPredicate(p : Predicate) : Boolean =
    TheoryRegistry.lookupSymbol(p) match {
      case Some(t) => t.modelGenPredicates contains p
      case None    => false
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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Trait for sorts that belong to a specific theory.
   */
  trait TheorySort extends Sort {

    /**
     * Query the theory that the sort belongs to.
     */
    def theory : Theory

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
   * Optionally, other theories that this theory depends on. Specified
   * dependencies will be loaded before this theory, but the preprocessors
   * of the dependencies will be called after the preprocessor of this theory.
   */
  val dependencies : Iterable[Theory] = List()

  /**
   * Dependencies closed under transitivity, i.e., also including the
   * dependencies of dependencies.
   */
  lazy val transitiveDependencies : Iterable[Theory] =
    (for (t <- dependencies.toSeq;
          s <- List(t) ++ t.transitiveDependencies) yield s).distinct

  /**
   * Optionally, a set of predicates used by the theory to tell the
   * <code>PresburgerModelFinder</code> about terms that will be handled
   * exclusively by this theory. If a proof goal in model generation mode
   * contains an atom <code>p(x)</code>, for <code>p</code> in this set,
   * then the <code>PresburgerModelFinder</code> will ignore <code>x</code>
   * when assigning concrete values to symbols.
   */
  val modelGenPredicates : Set[Predicate] = Set()

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  def iPreprocess(f : IFormula, signature : Signature)
                 : (IFormula, Signature) =
    (f, signature)

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */
  def preprocess(f : Conjunction, order : TermOrder) : Conjunction = f

  /**
   * Optionally, a post-processor that is applied to formulas output by the
   * prover, for instance to interpolants or the result of quantifier
   * elimination. This method will be applied to the raw formulas, before
   * calling <code>Internal2Inputabsy</code>.
   */
  def postprocess(f : Conjunction, order : TermOrder) : Conjunction = f

  /**
   * Optionally, a post-processor that is applied to formulas output by the
   * prover, for instance to interpolants or the result of quantifier
   * elimination. This method will be applied to the formula after
   * calling <code>Internal2Inputabsy</code>.
   */
  def iPostprocess(f : IFormula, signature : Signature) : IFormula = f

  /**
   * Optionally, simplifiers that are applied to formulas output by the
   * prover, for instance to interpolants or the result of quantifier. Such
   * simplifiers are invoked by with <code>ap.parser.Simplifier</code>.
   */
  def postSimplifiers : Seq[IExpression => IExpression] = List()

  /**
   * Optionally, a plugin for the reducer applied to formulas both before
   * and during proving.
   */
  val reducerPlugin : ReducerPluginFactory = IdentityReducerPluginFactory

  /**
   * Optionally, a function evaluating theory functions applied to concrete
   * arguments, represented as constructor terms.
   */
  def evalFun(f : IFunApp) : Option[ITerm] = None

  /**
   * Optionally, a function evaluating theory predicates applied to concrete
   * arguments, represented as constructor terms.
   */
  def evalPred(p : IAtom) : Option[Boolean] = None

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
