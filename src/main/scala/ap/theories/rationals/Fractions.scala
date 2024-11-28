/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.rationals

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories._
import ap.algebra.{Ring, RingWithDivision, IntegerRing, Field, OrderedRing}
import ap.types.{Sort, ProxySort, MonoSortedIFunction, MonoSortedPredicate}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.Signature
import ap.util.Debug

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

object Fractions {
    val AC = Debug.AC_RATIONAL
}

/**
 * The theory of fractions <code>s / t</code>, with <code>s, t</code>
 * taken from some ring. The theory uses an encoding in which the same
 * (fixed, but arbitrary) denominator is used for all expressions. The
 * range of considered denominators is described by the
 * <code>denomConstraint</code> argument over the variable <code>_0</code>.
 */
class Fractions(name            : String,
                underlyingRing  : Ring,
                denomConstraint : IFormula)
      extends Theory with RingWithDivision {

  import underlyingRing.{dom => RingSort, plus => ringPlus, mul => ringMul,
                         times => ringTimes, int2ring => ringInt2Ring}
  import Fractions.AC

  private val ringZero = underlyingRing.zero
  private val ringOne  = underlyingRing.one
  private val ringDom  = underlyingRing.dom

  /**
   * Method that can be overwritten in sub-classes to term concrete
   * fractions into canonical form.
   */
  protected def simplifyFraction(n : ITerm, d : ITerm) : (ITerm, ITerm) = (n, d)

  /**
   * Optionally, a stream of the constructor terms for this domain can be
   * defined (e.g., the fractions with co-prime numerator and denominator).
   */
  protected def individualsStream : Option[Stream[ITerm]] = None

  object FractionSort extends ProxySort (RingSort) with Theory.TheorySort {

    override val name = Fractions.this.name

    val theory = Fractions.this

    override lazy val individuals : Stream[ITerm] =
      individualsStream match {
        case None    => super.individuals
        case Some(s) => s
      }

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assign get ((d, this))

    private def augmentWithTerms(denomTerm : ITerm,
                                 assignment : MMap[(IdealInt, Sort), ITerm],
                                 allTerms : Set[(IdealInt, Sort)]) =
      for (p@(num, `dom`) <- allTerms;
           numTerm <- RingSort.decodeToTerm(num, assignment)) {
        val (n, d) = simplifyFraction(numTerm, denomTerm)
        assignment.put(p, IFunApp(frac, List(n, d)))
      }

    override def augmentModelTermSet(
                   model : Conjunction,
                   assignment : MMap[(IdealInt, Sort), ITerm],
                   allTerms : Set[(IdealInt, Sort)],
                   definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      model.predConj.lookupFunctionResult(_denom, List()) match {
        case Some(LinearCombination.Constant(d)) => {
          for (denomTerm <- RingSort.decodeToTerm(d, assignment))
            augmentWithTerms(denomTerm, assignment, allTerms)
        }
        case None =>
          augmentWithTerms(underlyingRing.one, assignment, allTerms)
        case _ =>
          throw new Exception("ill-formed model")
      }

      // TODO: add terms to definedTerms?
      super.augmentModelTermSet(model, assignment, allTerms, definedTerms)
    }
  }

  val dom : Sort = FractionSort

  /**
   * Function to embed ring elements in the ring of fractions.
   */
  val fromRing : IFunction =
    MonoSortedIFunction(name + "_fromRing", List(RingSort), dom,
                        true, false)

  /**
   * Function to represent fractions, where numerator and denominator
   * are expressions from the underlying ring
   */
  val frac : IFunction =
    MonoSortedIFunction(name + "_frac", List(RingSort, RingSort), dom,
                        true, false)

  /**
   * Function to represent sums of terms.
   */
  val addition : IFunction =
    MonoSortedIFunction(name + "_add", List(dom, dom), dom,
                        true, false)

  /**
   * Function to represent products of terms.
   */
  val multiplication : IFunction =
    MonoSortedIFunction(name + "_mul", List(dom, dom), dom,
                        true, false)

  /**
   * Function to represent a product of a ring term with a fraction
   * term.
   */
  val multWithRing : IFunction =
    MonoSortedIFunction(name + "_mulWithRing", List(RingSort, dom), dom,
                        true, false)

  /**
   * Function to represent a product of a fraction, represented using
   * numerator and denominator, with a fraction term.
   */
  val multWithFraction : IFunction =
    MonoSortedIFunction(name + "_mulWithFraction",
                        List(RingSort, RingSort, dom), dom,
                        true, false)

  /**
   * Function to represent division.
   */
  val division : IFunction =
    MonoSortedIFunction(name + "_div", List(dom, dom), dom,
                        true, false)

  /**
   * Extractor for fractions, where numerator and denominator
   * are expressions from the underlying ring.
   */
  object Fraction {
    def apply(num : ITerm, denom : ITerm) : ITerm =
      IFunApp(frac, List(num, denom))
    def unapply(t : ITerm) : Option[(ITerm, ITerm)] = t match {
      case IFunApp(`frac`, Seq(num, denom)) => Some((num, denom))
      case _                                => None
    }
  }

  /**
   * Extractor for ring elements embedded into the ring of fractions.
   */
  object Embedded {
    def apply(value : ITerm) : ITerm =
      IFunApp(fromRing, List(value))
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case IFunApp(`fromRing`, Seq(value)) => Some(value)
      case _                               => None
    }
  }

  /**
   * Function used internally to represent the unique denominator for all
   * fractions
   */
  val denom : IFunction =
    MonoSortedIFunction(name + "_denom", List(), RingSort,
                        true, false)

  private val denomT : ITerm = IFunApp(denom, Seq())

  val functions =
    List(frac, denom, fromRing, addition, multiplication,
         multWithRing, multWithFraction, division)

  def extraPredicates : Seq[IExpression.Predicate] = List()

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     extraPredicates = extraPredicates)

  val functionPredicateMapping = for (f <- functions) yield (f, funPredMap(f))
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  val functionalPredicates = predicates.toSet
  val plugin = None

  private val _denom : IExpression.Predicate = funPredMap(denom)

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value)
                           : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  import IExpression._

  def int2ring(s: ITerm): ITerm = fromRing(ringInt2Ring(s))

  val zero: ITerm = int2ring(0)
  val one : ITerm = int2ring(1)

  def plus(s: ITerm, t: ITerm): ITerm =
    addition(s, t)

  def mul(s: ITerm, t: ITerm): ITerm =
    multiplication(s, t)

  override def times(num : IdealInt, s : ITerm) : ITerm =
    multWithRing(ringInt2Ring(IIntLit(num)), s)

  override def times(num : ITerm, s : ITerm) : ITerm =
    multWithRing(ringInt2Ring(num), s)

  def div(s : ITerm, t : ITerm) : ITerm =
    division(s, t)

  def minus(s: ITerm): ITerm =
    multiplication(int2ring(-1), s)

  def fracPreproc(f : IFormula, signature : Signature)
               : (IFormula, Signature) = {
    val simplificationRules = Rewriter.combineRewritings(simplifiers)
    val encoder = new Encoder
//    println(f)
    val res0 = Rewriter.rewrite(f, simplificationRules).asInstanceOf[IFormula]
//    println(res0)
    val res1 = encoder.visit(res0, ()).asInstanceOf[IFormula]
//    println(res1)
    val res2 =
      res1 match {
        case INamedPart(name, res) if encoder.usedDenom(0) =>
          INamedPart(name,
                     ringDom.all((denomT === v(0, ringDom) &
                                    denomConstraint) ==> res))
        case res =>
          res
      }
    (res2, signature)
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                        : (IFormula, Signature) = {
    val (res, newSig) = fracPreproc(f, signature)
    IncompletenessChecker.visitWithoutResult(res, Context(()))
    (res, newSig)
  }

  protected def isNonZeroRingTerm(t : ITerm) : Boolean = false

  // TODO: only simplify fractional atoms
  private def simplifyExpr(t : IExpression) : IExpression =
    t match {
      // Simplification rules for literals
      case Fraction(num, `ringOne`) =>
        Embedded(num)
      case Fraction(num, denom)
        if num == denom && isNonZeroRingTerm(denom) =>
        one

      // Simplification rules for addition
      case IFunApp(`addition`, Seq(Embedded(num1), Embedded(num2))) =>
        Embedded(ringPlus(num1, num2))
      case IFunApp(`addition`,
                   Seq(Fraction(num1, denom1), Fraction(num2, denom2)))
        if denom1 == denom2 =>
        Fraction(ringPlus(num1, num2), denom1)
      case IFunApp(`addition`, Seq(t, `zero`)) =>
        t
      case IFunApp(`addition`, Seq(`zero`, t)) =>
        t

      // Simplification rules for multiplication
      case IFunApp(`multiplication`, Seq(s, Embedded(t))) =>
        multWithRing(t, s)
      case IFunApp(`multiplication`, Seq(Embedded(t), s)) =>
        multWithRing(t, s)

      case IFunApp(`multiplication`,
                   Seq(Fraction(num, denom), s)) =>
        multWithFraction(num, denom, s)
      case IFunApp(`multiplication`,
                   Seq(s, Fraction(num, denom))) =>
        multWithFraction(num, denom, s)

      case IFunApp(`multiplication`,
                   Seq(IFunApp(`multWithRing`, Seq(r, t)), s)) =>
        multWithRing(r, multiplication(t, s))
      case IFunApp(`multiplication`,
                   Seq(s, IFunApp(`multWithRing`, Seq(r, t)))) =>
        multWithRing(r, multiplication(s, t))

      case IFunApp(`multiplication`,
                   Seq(IFunApp(`multWithFraction`, Seq(num, denom, t)), s)) =>
        multWithFraction(num, denom, multiplication(t, s))
      case IFunApp(`multiplication`,
                   Seq(s, IFunApp(`multWithFraction`, Seq(num, denom, t)))) =>
        multWithFraction(num, denom, multiplication(s, t))

      // Simplification rules for multiplication with ring element
      case IFunApp(`multWithRing`, Seq(`ringOne`, t)) =>
        t
      case IFunApp(`multWithRing`, Seq(`ringZero`, t)) =>
        zero
      case IFunApp(`multWithRing`, Seq(s, Embedded(t))) =>
        Embedded(ringMul(s, t))
      case IFunApp(`multWithRing`, Seq(s, Fraction(num, denom))) =>
        Fraction(ringMul(s, num), denom)

      case IFunApp(`multWithRing`,
                   Seq(t1, IFunApp(`multWithRing`, Seq(t2, s)))) =>
        multWithRing(ringMul(t1, t2), s)
      case IFunApp(`multWithRing`,
                   Seq(t, IFunApp(`multWithFraction`, Seq(num, denom, s)))) =>
        multWithFraction(ringMul(t, num), denom, s)
      case IFunApp(`multWithRing`,
                   Seq(t, IFunApp(`addition`, Seq(s1, s2)))) =>
        addition(multWithRing(t, s1), multWithRing(t, s2))

      // Simplification rules for multiplication with fraction
      case IFunApp(`multWithFraction`, Seq(num, denom, t))
        if num == denom && isNonZeroRingTerm(denom) =>
        t
      case IFunApp(`multWithFraction`, Seq(num, `ringOne`, t)) =>
        multWithRing(num, t)
      case IFunApp(`multWithFraction`, Seq(`ringZero`, denom, t))
        if isNonZeroRingTerm(denom) =>
        zero

      case IFunApp(`multWithFraction`,
                   Seq(num1, denom1,
                       IFunApp(`multWithFraction`, Seq(num2, denom2, s)))) =>
        multWithFraction(ringMul(num1, num2), ringMul(denom1, denom2), s)
      case IFunApp(`multWithFraction`,
                   Seq(num, denom, IFunApp(`multWithRing`, Seq(t, s)))) =>
        multWithFraction(ringMul(num, t), denom, s)
      case IFunApp(`multWithFraction`,
                   Seq(num, denom, IFunApp(`addition`, Seq(s1, s2)))) =>
        addition(multWithFraction(num, denom, s1),
                 multWithFraction(num, denom, s2))

      // Simplification rules for division
      case IFunApp(`division`, Seq(num, `one`)) =>
        num
      case IFunApp(`division`,
                   Seq(Fraction(num1, denom1), Fraction(num2, denom2)))
        if isNonZeroRingTerm(denom2) =>
        Fraction(ringMul(num1, denom2), ringMul(denom1, num2))
      case IFunApp(`division`,
                   Seq(Fraction(num1, denom1), Embedded(num2))) =>
        Fraction(num1, ringMul(num2, denom1))
      case IFunApp(`division`,
                   Seq(Embedded(num1), Fraction(num2, denom2)))
        if isNonZeroRingTerm(denom2) =>
        Fraction(ringMul(num1, denom2), num2)
      case IFunApp(`division`,
                   Seq(Embedded(num), Embedded(denom))) =>
        Fraction(num, denom)
      case IFunApp(`division`,
                   Seq(num : ITerm, Embedded(denom))) =>
        multWithFraction(ringOne, denom, num)

      // Arithmetic simplification
      case Eq(Embedded(s), Embedded(t)) =>
        s === t
      case Eq(Fraction(num1, denom1), Fraction(num2, denom2))
        if isNonZeroRingTerm(denom1) && isNonZeroRingTerm(denom2) =>
        ringMul(num1, denom2) === ringMul(num2, denom1)

      case t => t
    }

  protected def simplifiers = List(simplifyExpr _)

  private class Encoder extends CollectingVisitor[Unit, IExpression] {
    val usedDenom = Array(false)
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = 
      encodeExpr(t, subres, usedDenom)
  }

  protected def encodeExpr(t         : IExpression,
                           subres    : Seq[IExpression],
                           usedDenom : Array[Boolean]) : IExpression = {
    t match {
      case IFunApp(`fromRing`, _) => {
        val Seq(num : ITerm) = subres
        usedDenom(0) = true
        ringMul(denomT, num)
      }
      case IFunApp(`frac`, _) => {
        // num / den =
        // (num / den) * denom / denom =
        // (num * (denom / den)) / denom
        val Seq(num : ITerm, den : ITerm) = subres
        usedDenom(0) = true
        dom.eps(dom.ex(
                  (denomT === ringMul(v(0, dom), shiftVars(den, 2))) &
                    (v(1, dom) === ringMul(v(0, dom), shiftVars(num, 2)))))
      }
      case IFunApp(`denom`, _) => {
        usedDenom(0) = true
        t
      }

      case IFunApp(`addition`, _) => {
        val Seq(s : ITerm, t : ITerm) = subres
        ringPlus(s, t)
      }

      case IFunApp(`multiplication`, _) => {
        // (s / denom) * (t / denom) =
        // s * t / denom^2 =
        // (s * t / denom) / denom
        usedDenom(0) = true
        val Seq(s : ITerm, t : ITerm) = subres
        dom.eps(ringDom.ex((denomT === v(0, ringDom)) & denomConstraint &
                             (ringMul(v(0, ringDom), v(1, dom)) ===
                                ringMul(shiftVars(s, 2), shiftVars(t, 2)))))
      }

      case IFunApp(`multWithRing`, _) => {
        val Seq(s : ITerm, t : ITerm) = subres
        ringMul(s, t)
      }

      case IFunApp(`multWithFraction`, _) => {
        // (num / den) * (s / denom) =
        // (num * s / den) / denom
        val Seq(num : ITerm, den : ITerm, s : ITerm) = subres
        dom.eps(ringMul(shiftVars(num, 1), shiftVars(s, 1)) ===
                  ringMul(v(0, dom), shiftVars(den, 1)))
      }

      case IFunApp(`division`, _) => {
        // (s / denom) / (t / denom) =
        // (s / denom) * (denom / t) =
        // (s * denom / t) / denom
        usedDenom(0) = true
        val Seq(s : ITerm, t : ITerm) = subres
        dom.eps(ringDom.ex((denomT === v(0, ringDom)) & denomConstraint &
                             (ringMul(shiftVars(t, 2), v(1, dom)) ===
                                ringMul(shiftVars(s, 2), v(0, ringDom)))))
      }

      case _ =>
        (t update subres)
    }
  }

  /////////////////////////////////////////////////////////////////////////////

  // TODO: is the following approach only applicable for rationals??

  private def backtranslateAtoms(e : IExpression) : IExpression = e match {
    case Eq(`denomT`, ITimes(coeff, t))
      if !coeff.isZero && !termNeedsRewr(t) => {
      t === Fraction(ringOne, coeff)
    }
    case Eq(ITimes(coeff1, `denomT`), ITimes(coeff2, t))
      if !coeff2.isZero && !termNeedsRewr(t) => {
      t === Fraction(coeff1, coeff2)
    }
    case Eq(ITimes(coeff2, t), ITimes(coeff1, `denomT`))
      if !coeff2.isZero && !termNeedsRewr(t) => {
      t === Fraction(coeff1, coeff2)
    }

    case Eq(t1, t2) if termNeedsRewr(t1) || termNeedsRewr(t2) => {
      val (s1, r1) = divByDenom(t1)
      val (s2, r2) = divByDenom(t2)
      //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
      Debug.assertInt(AC, r1 == r2)
      //-END-ASSERTION-////////////////////////////////////////////////////////
      s1 === s2
    }
    case EqZ(t) if termNeedsRewr(t) => {
      val (s, r) = divByDenom(t)
      //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
      Debug.assertInt(AC, r.isZero)
      //-END-ASSERTION-////////////////////////////////////////////////////////
      s === zero
    }
    case t => t
  }

  protected def termNeedsRewr(t : ITerm) : Boolean = {
    import IExpression.Sort.:::
    t match {
      case IPlus(_ ::: `dom`, _)  => true
      case IPlus(_, _ ::: `dom`)  => true
      case ITimes(_, _ ::: `dom`) => true
      case IPlus(s, t)            => termNeedsRewr(s) || termNeedsRewr(t)
      case ITimes(_, s)           => termNeedsRewr(s)
      case `denomT`               => true
      case _                      => false
    }
  }

  /**
   * Divide each term of a sum by the <code>denom()</code> term, rewriting
   * accordingly. Constant terms are dropped and their sum is returned
   * as the second result.
   */
  def divByDenom(t : ITerm) : (ITerm, IdealInt) = {
    t match {
      case IPlus(t1, t2) => {
        val (s1, r1) = divByDenom(t1)
        val (s2, r2) = divByDenom(t2)
        (addition(s1, s2), r1 + r2)
      }
      case ITimes(coeff, t1) => {
        val (s1, r1) = divByDenom(t1)
        (multWithRing(ringInt2Ring(coeff), s1), coeff * r1)
      }
      case `denomT` =>
        (one, 0)
      case IIntLit(value) =>
        (zero, value)
      case t =>
        (t, 0)
    }
  }

  override def postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ simplifiers ++ List(backtranslateAtoms _)

  /////////////////////////////////////////////////////////////////////////////

  /**
   * The theory is not complete for the full first-order case; check
   * whether the denom function occurs in the scope of a quantifier.
   */
  protected object IncompletenessChecker
            extends ContextAwareVisitor[Unit, Unit] {
    def postVisit(t : IExpression, ctxt : Context[Unit],
                  subres : Seq[Unit]) : Unit = t match {
      case ISortedQuantified(q, `dom`, _)
          if (ctxt.polarity match {
                case 0 => true
                case 1 => q == Quantifier.EX
                case -1 => q == Quantifier.ALL
              }) =>
        throw new Exception(
          "Universal quantifiers over fractions/rationals are currently not supported")

/*
      case IFunApp(`denom`, _) if ctxt.binders contains Context.EX => {
        Incompleteness.set
        ()
      }
 */
      case _ =>
        ()
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = name

}

/**
 * The theory of fractions <code>s / t</code>, with <code>s, t</code>
 * taken from some ordered ring.
 */
class OrderedFractions(name            : String,
                       underlyingRing  : OrderedRing,
                       denomConstraint : IFormula)
      extends Fractions(name, underlyingRing, denomConstraint)
      with OrderedRing {

  import IExpression._
  import underlyingRing.{int2ring => ringInt2Ring,
                         lt => ringLt, leq => ringLeq}
  import Fractions.AC

  /**
   * Less-than predicate.
   */
  lazy val lessThan : Predicate =
    MonoSortedPredicate(name + "_lt", List(dom, dom))

  /**
   * Less-than-or-equal predicate.
   */
  lazy val lessThanOrEqual : Predicate =
    MonoSortedPredicate(name + "_leq", List(dom, dom))

  override def extraPredicates = List(lessThan, lessThanOrEqual)

  def lt(s : ITerm, t : ITerm) : IFormula = lessThan(s, t)

  def leq(s : ITerm, t : ITerm) : IFormula = lessThanOrEqual(s, t)

  override protected def simplifiers =
    super.simplifiers ++ List(simplifyIneqs _)

  override def postSimplifiers : Seq[IExpression => IExpression] =
    super.postSimplifiers ++ List(backtranslateIneqs _)

  private def simplifyIneqs(t : IExpression) : IExpression =
    t match {
      case IAtom(`lessThan`, Seq(Embedded(s), Embedded(t))) =>
        ringLt(s, t)
      case IAtom(`lessThanOrEqual`, Seq(Embedded(s), Embedded(t))) =>
        ringLeq(s, t)
      case t => t
    }

  override protected
    def encodeExpr(t         : IExpression,
                   subres    : Seq[IExpression],
                   usedDenom : Array[Boolean]) : IExpression = {
      (t, subres) match {
        case (IAtom(`lessThan`, _), Seq(s : ITerm, t : ITerm)) =>
          ringLt(s, t)
        case (IAtom(`lessThanOrEqual`, _), Seq(s : ITerm, t : ITerm)) =>
          ringLeq(s, t)
        case _ =>
          super.encodeExpr(t, subres, usedDenom)
      }
    }

  private def backtranslateIneqs(e : IExpression) : IExpression = e match {
    case GeqZ(t) if termNeedsRewr(t) => {
      val (s, r) = divByDenom(t)
      r.signum match {
        case -1 => lessThan(zero, s)
        case 0  => lessThanOrEqual(zero, s)
        case 1  => throw new Exception(
                     "cannot back-translate rational inequality " + e)
      }
    }
    case t => t
  }

}
