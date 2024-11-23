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

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

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

  val functions =
    List(frac, denom, fromRing, addition, multiplication,
         multWithRing, division)

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
    val simplifier = new Simplifier
    val encoder = new Encoder
//    println(f)
    val res0 = simplifier.visit(f, ()).asInstanceOf[IFormula]
//    println(res0)
    val res1 = encoder.visit(res0, ()).asInstanceOf[IFormula]
//    println(res1)
    val res2 =
      res1 match {
        case INamedPart(name, res) if encoder.usedDenom(0) =>
          INamedPart(name,
                     ringDom.all((denom() === v(0, ringDom) &
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

  private class Simplifier extends CollectingVisitor[Unit, IExpression] {

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      simplifyExpr(t, subres)
  }

  protected def simplifyExpr(t : IExpression,
                             subres : Seq[IExpression]) : IExpression = {
    import GroebnerMultiplication.{mult => GroebnerMult}

      (t, subres) match {

        // Simplification rules for addition
        case (IFunApp(`addition`, _),
              Seq(Embedded(num1), Embedded(num2))) =>
          Embedded(ringPlus(num1, num2))
        case (IFunApp(`addition`, _),
              Seq(Fraction(num1, denom1), Fraction(num2, denom2)))
          if denom1 == denom2 =>
          Fraction(ringPlus(num1, num2), denom1)

        // Simplification rules for multiplication
        case (IFunApp(`multiplication`, _),
              Seq(Fraction(num1, denom1), Fraction(num2, denom2))) =>
          Fraction(ringMul(num1, num2), ringMul(denom1, denom2))
        case (IFunApp(`multiplication`, _),
              Seq(Embedded(num1), Fraction(num2, denom2))) =>
          Fraction(ringMul(num1, num2), denom2)
        case (IFunApp(`multiplication`, _),
              Seq(Fraction(num1, denom1), Embedded(num2))) =>
          Fraction(ringMul(num2, num1), denom1)
        case (IFunApp(`multiplication`, _),
              Seq(Embedded(num1), Embedded(num2))) =>
          Embedded(ringMul(num1, num2))

        case (IFunApp(`multiplication`, _), Seq(t, `one`)) =>
          t
        case (IFunApp(`multiplication`, _), Seq(t, `zero`)) =>
          zero
        case (IFunApp(`multiplication`, _), Seq(`one`, t)) =>
          t
        case (IFunApp(`multiplication`, _), Seq(`zero`, t)) =>
          zero

        case (IFunApp(`multiplication`, _),
              Seq(Embedded(num1),
                  IFunApp(`multiplication`, Seq(Embedded(num2), t)))) =>
          multiplication(Embedded(ringMul(num1, num2)), t)

        // Simplification rules for division
        case (IFunApp(`division`, _),
              Seq(num, `one`)) =>
          num
        case (IFunApp(`division`, _),
              Seq(Fraction(num1, denom1), Fraction(num2, denom2))) =>
          Fraction(ringMul(num1, denom2), ringMul(denom1, num2))
        case (IFunApp(`division`, _),
              Seq(Fraction(num1, denom1), Embedded(num2))) =>
          Fraction(num1, ringMul(num2, denom1))
        case (IFunApp(`division`, _),
              Seq(Embedded(num1), Fraction(num2, denom2))) =>
          Fraction(ringMul(num1, denom2), num2)
        case (IFunApp(`division`, _),
              Seq(Embedded(num), Embedded(denom))) =>
          Fraction(num, denom)
        case (IFunApp(`division`, _),
              Seq(num : ITerm, Embedded(denom))) =>
          multiplication(num, Fraction(ringOne, denom))

        // Arithmetic simplification
        case (IEquation(_, _)
              Seq(Embedded(s), Embedded(t))) =>
          s === t
        case (IIntFormula(IIntRelation.EqZero, _),
              Seq(Difference(Embedded(s), Embedded(t)))) =>
          s === t

        case _ =>
          t update subres
      }
    }

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
        ringMul(denom(), num)
      }
      case IFunApp(`frac`, _) => {
        val Seq(num : ITerm, den : ITerm) = subres
        usedDenom(0) = true
        dom.eps(dom.ex(
                  (denom() === ringMul(v(0, dom), shiftVars(den, 2))) &
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
        dom.eps(ringDom.ex((denom() === v(0, ringDom)) & denomConstraint &
                             (ringMul(v(0, ringDom), v(1, dom)) ===
                                ringMul(shiftVars(s, 2), shiftVars(t, 2)))))
      }

      case IFunApp(`multWithRing`, _) => {
        val Seq(s : ITerm, t : ITerm) = subres
        ringMul(s, t)
      }

      case IFunApp(`division`, _) => {
        // (s / denom) / (t / denom) =
        // (s / denom) * (denom / t) =
        // (s * denom / t) / denom
        usedDenom(0) = true
        val Seq(s : ITerm, t : ITerm) = subres
        dom.eps(ringDom.ex((denom() === v(0, ringDom)) & denomConstraint &
                             (ringMul(shiftVars(t, 2), v(1, dom)) ===
                                ringMul(shiftVars(s, 2), v(0, ringDom)))))
      }

      case _ =>
        (t update subres)
    }
  }

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

  override protected
    def simplifyExpr(t : IExpression,
                     subres : Seq[IExpression]) : IExpression = {
      (t, subres) match {
        case (IAtom(`lessThan`, _),
              Seq(Embedded(s), Embedded(t))) =>
          ringLt(s, t)
        case (IAtom(`lessThanOrEqual`, _),
              Seq(Embedded(s), Embedded(t))) =>
          ringLeq(s, t)
        case _ =>
          super.simplifyExpr(t, subres)
      }
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

}
