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
import ap.types.{Sort, ProxySort, MonoSortedIFunction}
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
class Fractions(name : String,
                underlyingRing : Ring,
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
   * Function to embed integers in the ring of fractions
   */
  val int : IFunction =
    MonoSortedIFunction(name + "_int", List(Sort.Integer), dom,
                        true, true)

  /**
   * Function to represent fractions, where numerator and denominator
   * are expressions from the underlying ring
   */
  val frac : IFunction =
    MonoSortedIFunction(name + "_frac", List(RingSort, RingSort), dom,
                        true, true)

  /**
   * Extractor for fractions, where numerator and denominator
   * are expressions from the underlying ring
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
   * Function used internally to represent the unique denominator for all
   * fractions
   */
  val denom : IFunction =
    MonoSortedIFunction(name + "_denom", List(), RingSort,
                        true, false)

  val functions = List(frac, denom, int)

  val (predicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions)

  val functionPredicateMapping = functions zip predicates
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  val functionalPredicates = predicates.toSet
  val plugin = None

  private val _denom : IExpression.Predicate = predicates(1)

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value)
                           : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }


  import IExpression._

  def int2ring(s: ITerm): ITerm = int(s)
//    frac(underlyingRing.int2ring(s), ringOne)

  val zero: ITerm = int2ring(0)   // frac(ringZero, ringOne)
  val one : ITerm = int2ring(1)   // frac(ringOne, ringOne)

  def plus(s: ITerm, t: ITerm): ITerm = (s, t) match {
    case (IFunApp(`int`, Seq(num1)),
          IFunApp(`int`, Seq(num2))) =>
      int(num1 +++ num2)
    case (IFunApp(`frac`, Seq(num1, denom1)),
          IFunApp(`frac`, Seq(num2, denom2))) if denom1 == denom2 =>
      frac(ringPlus(num1, num2), denom1)
    case _ =>
      ringPlus(s, t)
  }

  override def times(num : IdealInt, s : ITerm) : ITerm = s match {
    case IFunApp(`int`, Seq(n)) =>
      int(n *** num)
    case IFunApp(`frac`, Seq(n, d)) =>
      frac(ringTimes(num, n), d)
    case s =>
      ringTimes(num, s)
  }

  def mul(s: ITerm, t: ITerm): ITerm = (s, t) match {
    case (IFunApp(`frac`, Seq(num1, denom1)),
          IFunApp(`frac`, Seq(num2, denom2))) =>
      frac(ringMul(num1, num2), ringMul(denom1, denom2))
    case (IFunApp(`int`,  Seq(num1)),
          IFunApp(`frac`, Seq(num2, denom2))) =>
      frac(ringMul(ringInt2Ring(num1), num2), denom2)
    case (IFunApp(`frac`, Seq(num1, denom1)),
          IFunApp(`int`,  Seq(num2))) =>
      frac(ringMul(num1, ringInt2Ring(num2)), denom1)
    case (IFunApp(`int`, Seq(Const(num))), t) =>
      times(num, t)
    case (t, IFunApp(`int`, Seq(Const(num)))) =>
      times(num, t)
    case (IFunApp(`int`, Seq(num1)), IFunApp(`int`, Seq(num2))) =>
      int(GroebnerMultiplication.mult(num1, num2))
    case (s, t) =>
      // (s / denom) * (t / denom) =
      // s * t / denom^2 =
      // (s * t / denom) / denom
      dom.eps(ringDom.ex((denom() === v(0, ringDom)) & denomConstraint &
                           (ringMul(v(0, ringDom), v(1, dom)) ===
                              ringMul(shiftVars(s, 2), shiftVars(t, 2)))))
  }

  def div(s : ITerm, t : ITerm) : ITerm = t match {
    case IFunApp(`int`, Seq(Const(IdealInt.ONE))) =>
      s
    case IFunApp(`int`, Seq(n)) =>
      mul(s, frac(ringOne, ringInt2Ring(n)))
    case IFunApp(`frac`, Seq(n, d)) =>
      mul(s, frac(d, n))
    case t =>
      // (s / denom) / (t / denom) =
      // (s / denom) * (denom / t) =
      // (s * denom / t) / denom
      dom.eps(ringDom.ex((denom() === v(0, ringDom)) & denomConstraint &
                           (ringMul(shiftVars(t, 2), v(1, dom)) ===
                              ringMul(shiftVars(s, 2), v(0, ringDom)))))
  }

  def minus(s: ITerm): ITerm = s match {
    case IFunApp(`int`, Seq(n)) =>
      int(-n)
    case IFunApp(`frac`, Seq(n, d)) =>
      frac(underlyingRing.minus(n), d)
    case s =>
      underlyingRing.minus(s)
  }

  def fracPreproc(f : IFormula, signature : Signature)
               : (IFormula, Signature) = {
    val visitor =
      new Preprocessor
    val res =
      visitor.visit(f, ()).asInstanceOf[IFormula]
    val res2 =
      res match {
        case INamedPart(name, res) if visitor.usedDenom =>
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

  private class Preprocessor extends CollectingVisitor[Unit, IExpression] {
    var usedDenom = false
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`int`, _) =>
        subres match {
          case Seq(num : ITerm) => {
            usedDenom = true
            ringMul(denom(), ringInt2Ring(num))
          }
        }
      case IFunApp(`frac`, _) =>
        subres match {
          case Seq(num : ITerm, den : ITerm) => {
            usedDenom = true
            dom.eps(dom.ex(
                      (denom() === ringMul(v(0, dom), shiftVars(den, 2))) &
                        (v(1, dom) === ringMul(v(0, dom), shiftVars(num, 2)))))
          }
        }
      case IFunApp(`denom`, _) => {
        usedDenom = true
        t
      }
      case _ =>
        (t update subres) match {
          case ITimes(coeff, IFunApp(`int`, Seq(s))) =>
            int(coeff * s)
          case IPlus(IFunApp(`int`, Seq(s)), IFunApp(`int`, Seq(t))) =>
            int(s + t)
          case IIntFormula(r, IFunApp(`int`, Seq(s))) =>
            IIntFormula(r, s)
          case res =>
            res
        }
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
