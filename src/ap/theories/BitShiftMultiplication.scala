/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014-2018 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.{Formula, TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.parameters.Param

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}

object MulTheory {

  /**
   * Extractor recognising the <code>mul</code> function of
   * any multiplication theory.
   */
  object Mul {
    def unapply(fun : IFunction) : Boolean =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : MulTheory) => fun == t.mul
        case _ => false
      }
  }

}

trait MulTheory extends Theory {

  /**
   * Symbol representing proper (non-linear) multiplication
   */
  val mul : IFunction

  /**
   * Multiply two terms, using the <code>mul</code> function if necessary;
   * if any of the two terms is constant, normal Presburger
   * multiplication will be used.
   */
  def mult(t1 : ITerm, t2 : ITerm) : ITerm =
    try {
      t1 * t2
    } catch {
      case _ : IllegalArgumentException => IFunApp(mul, List(t1, t2))
    }

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._

  /**
   * Euclidian division
   */
  def eDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm) && Const.unapply(denomTerm).isDefined) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      val v0Denom = mult(v(0), denom)
      eps((v0Denom <= num) & (v0Denom > num - abs(denom)))
    } else {
      // avoid duplication of the numerator by introducing a quantifier

      val num = VariableShiftVisitor(numTerm, 0, 4)
      val denom = VariableShiftVisitor(denomTerm, 0, 4)

      eps(ex(ex(ex((v(0) === num) &
                   (v(1) === mult(v(3), v(2))) &
                   (v(2) === denom) &
                   (v(1) <= v(0)) & (v(1) > v(0) - abs(v(2)))))))
    }

  /**
   * Euclidian remainder
   */
  def eMod(numTerm : ITerm, denomTerm : ITerm) : ITerm = {
    val num = VariableShiftVisitor(numTerm, 0, 1)
    val denom = VariableShiftVisitor(denomTerm, 0, 1)

    eps((v(0) >= 0) & (v(0) < abs(denom)) &
        ex(VariableShiftVisitor(num, 0, 1) ===
             mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
  }

  /**
   * Truncation division
   */
  def tDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm) && Const.unapply(denomTerm).isDefined) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      val rem = num - mult(v(0), denom)
      eps((rem < abs(denom)) & (-rem < abs(denom)) &
          ((rem > 0) ==> (num > 0)) & ((rem < 0) ==> (num < 0)))
    } else {
      // avoid duplication of terms by introducing quantifiers

      val num = VariableShiftVisitor(numTerm, 0, 4)
      val denom = VariableShiftVisitor(denomTerm, 0, 4)

      eps(ex(ex(ex((v(0) === num) &
                   (v(1) === v(0) - mult(v(3), v(2))) &
                   (v(2) === denom) &
                   (v(1) < abs(v(2))) & (-v(1) < abs(v(2))) &
                   ((v(1) > 0) ==> (v(0) > 0)) & ((v(1) < 0) ==> (v(0) < 0))))))
    }

  /**
   * Truncation remainder
   */
  def tMod(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm)) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      eps((v(0) < abs(denom)) & (-v(0) < abs(denom)) &
          ((v(0) > 0) ==> (num > 0)) & ((v(0) < 0) ==> (num < 0)) &
          ex(VariableShiftVisitor(num, 0, 1) ===
             mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
    } else {
      // avoid duplication of the numerator by introducing a quantifier

      val num = VariableShiftVisitor(numTerm, 0, 2)
      val denom = VariableShiftVisitor(denomTerm, 0, 2)

      eps(ex((v(0) === num) &
             (v(1) < abs(denom)) & (-v(1) < abs(denom)) &
             ((v(1) > 0) ==> (v(0) > 0)) & ((v(1) < 0) ==> (v(0) < 0)) &
             ex(v(1) === mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(2))))
    }

  /**
   * Floor division
   */
  def fDiv(numTerm : ITerm, denomTerm : ITerm) : ITerm =
    if (isSimpleTerm(numTerm)) {
      val num = VariableShiftVisitor(numTerm, 0, 1)
      val denom = VariableShiftVisitor(denomTerm, 0, 1)

      val rem = num - mult(v(0), denom)
      eps((rem < abs(denom)) & (-rem < abs(denom)) &
          ((rem > 0) ==> (denom > 0)) & ((rem < 0) ==> (denom < 0)))
    } else {
      // avoid duplication of the numerator by introducing a quantifier

      val num = VariableShiftVisitor(numTerm, 0, 2)
      val denom = VariableShiftVisitor(denomTerm, 0, 2)

      val rem = v(0) - mult(v(1), denom)
      eps(ex((v(0) === num) &
             (rem < abs(denom)) & (-rem < abs(denom)) &
             ((rem > 0) ==> (denom > 0)) & ((rem < 0) ==> (denom < 0))))
    }

  /**
   * Floor remainder
   */
  def fMod(numTerm : ITerm, denomTerm : ITerm) : ITerm = {
    val num = VariableShiftVisitor(numTerm, 0, 1)
    val denom = VariableShiftVisitor(denomTerm, 0, 1)

    eps((v(0) < abs(denom)) & (-v(0) < abs(denom)) &
        ((v(0) > 0) ==> (denom > 0)) & ((v(0) < 0) ==> (denom < 0)) &
        ex(VariableShiftVisitor(num, 0, 1) ===
           mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1)))
  }

  /**
   * Exponentiation, with non-negative exponent
   */
  def pow(basis : ITerm, expTerm : ITerm) : ITerm = expTerm match {
    case Const(exp) => exp.signum match {
      case -1 =>
        throw new IllegalArgumentException
      case 0 =>
        1
      case 1 =>
        (for (_ <- 0 until exp.intValueSafe) yield basis) reduceLeft (mult _)
    }
    case _ =>
      throw new IllegalArgumentException
  }

  //////////////////////////////////////////////////////////////////////////////

  class RichMulTerm(term : ITerm) {
    /**
     * Multiply two terms, using the <code>MulTheory.mul</code> function
     * if necessary;
     * if any of the two terms is constant, normal Presburger
     * multiplication will be used.
     */
    def **(that : ITerm) : ITerm  = mult(term, that)

    /**
     * Euclidian division
     */
    def /(that : ITerm) : ITerm  = MulTheory.this.eDiv(term, that)

    /**
     * Euclidian remainder
     */
    def %(that : ITerm) : ITerm  = MulTheory.this.eMod(term, that)

    /**
     * Euclidian division
     */
    def eDiv(that : ITerm) : ITerm = MulTheory.this.eDiv(term, that)

    /**
     * Euclidian remainder
     */
    def eMod(that : ITerm) : ITerm = MulTheory.this.eMod(term, that)

    /**
     * Truncation division
     */
    def tDiv(that : ITerm) : ITerm = MulTheory.this.tDiv(term, that)

    /**
     * Truncation remainder
     */
    def tMod(that : ITerm) : ITerm = MulTheory.this.tMod(term, that)

    /**
     * Floor division
     */
    def fDiv(that : ITerm) : ITerm = MulTheory.this.fDiv(term, that)

    /**
     * Floor remainder
     */
    def fMod(that : ITerm) : ITerm = MulTheory.this.fMod(term, that)

    /**
     * Exponentiation, with non-negative exponent. Note that <code>^</code>
     * binds only weakly in Scala, so usually one has to write <code>(x^2)</code>
     * with parentheses.
     */
    def ^(exp : ITerm) : ITerm = pow(term, exp)
  }

  implicit def convert2RichMulTerm(term : ITerm) = new RichMulTerm(term)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : IExpression) : IExpression =
    MulConverter.visit(expr, ())

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : ITerm) : ITerm =
    MulConverter.visit(expr, ()).asInstanceOf[ITerm]

  /**
   * Convert the given expression to this multiplication theory
   */
  def convert(expr : IFormula) : IFormula =
    MulConverter.visit(expr, ()).asInstanceOf[IFormula]

  private object MulConverter extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(f, _) => (TheoryRegistry lookupSymbol f) match {
        case Some(mulTheory : MulTheory) if (f == mulTheory.mul && f != mul) =>
          IFunApp(mul, for (e <- subres.toList) yield e.asInstanceOf[ITerm])
        case _ =>
          t update subres
      }
      case _ =>
        t update subres
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Multiplication by means of axioms describing shift-and-add
 */
object BitShiftMultiplication extends MulTheory {

  import IExpression._

  private val partial = false
  
  val mul = new IFunction("mul", 2, partial, false)
  
  val functions = List(mul)

    /*
        \forall int x; {mul(x, 0)} mul(x, 0) = 0
      &
        \forall int x; {mul(x, -1)} mul(x, -1) = -x
      &
        \forall int x, y, res; {mul(x, y)}
          ((y >= 1 | y <= -2) -> mul(x, y) = res ->
              \exists int l, n, subres; (
                 mul(2*x, l) = subres &
                 y = 2*l + n & (
                   n = 0 & res = subres
                   |
                   n = 1 & res = subres + x
       )))
    */

  val (predicates, axioms, _, _) =
      Theory.genAxioms(theoryFunctions = functions,
                       theoryAxioms =
                        all(ITrigger(List(mul(v(0), 0)),
                                     mul(v(0), 0) === 0)) &
                        all(ITrigger(List(mul(v(0), -1)),
                                     mul(v(0), -1) === -v(0))) &
                        all(all(all(
                          ITrigger(List(mul(v(0), v(1))),
                            (((v(1) >= 1 | v(1) <= -2) & mul(v(0), v(1)) === v(2)) ==>
                              ex(ex(ex(
                                 (mul(2*v(3), v(0)) === v(2)) &
                                 (v(4) === 2*v(0) + v(1)) & (
                                   (v(1) === 0 & v(5) === v(2))
                                   |
                                   (v(1) === 1 & v(5) === v(2) + v(3))
                                  ))))))))))

  val totalityAxioms = Conjunction.TRUE

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val functionalPredicates = predicates.toSet

  override val singleInstantiationPredicates = predicates.toSet

  private def _mul = predicates(0)

  val functionPredicateMapping = List((mul, _mul))

  val triggerRelevantFunctions : Set[IFunction] = Set()

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    theories match {
      case Seq(BitShiftMultiplication) => true
      case _ => false
    }

  val plugin = Some(new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      if (Param.PROOF_CONSTRUCTION(goal.settings)) {
        List()
      } else {

        // check if we find any mul-literal with concrete operands;
        // in this case, the literal can be replaced with a simple
        // equation

        implicit val order = goal.order
        import TerForConvenience._

        val (newEqs, atomsToRemove) =
          (for (a <- goal.facts.predConj.positiveLitsWithPred(_mul);
                if (a(0).isConstant || a(1).isConstant))
           yield (a(0) * a(1) === a(2), a)).unzip

        if (newEqs.isEmpty) {
          List()
        } else {
          List(Plugin.AddFormula(conj(newEqs).negate),
               Plugin.RemoveFacts(conj(atomsToRemove)))
        }

      }

    def generateAxioms(goal : Goal)
                      : Option[(Conjunction, Conjunction)] = None
  })

  TheoryRegistry register this

  override def toString = "BitShiftMultiplication"

}
