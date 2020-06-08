/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.rationals

import ap.parser._
import ap.basetypes.IdealInt
import ap.theories._
import ap.theories.algebra.{Ring, PseudoRing, IntegerRing}
import ap.types.{Sort, ProxySort, MonoSortedIFunction}
import ap.terfor.conjunctions.Conjunction
import ap.Signature

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
      extends Theory with PseudoRing {

  import underlyingRing.{dom => RingSort, mul => ringMul}

  val dom = new ProxySort (RingSort) {
    override val name = Fractions.this.name
    // TODO: decode fractions
  }

  /**
   * Function to represent fractions, where numerator and denominator
   * are expressions from the underlying ring
   */
  val frac =
    MonoSortedIFunction(name + "_frac", List(RingSort, RingSort), dom,
                        true, false)

  /**
   * Function used internally to represent the unique denominator for all
   * fractions
   */
  val denom =
    MonoSortedIFunction(name + "_denom", List(), RingSort,
                        true, false)

  val functions = List(frac, denom)

  val (predicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions)

  val functionPredicateMapping = functions zip predicates
  val totalityAxioms = Conjunction.TRUE
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  val functionalPredicates = predicates.toSet
  val plugin = None

// TODO
//   override val dependencies = List(GroebnerMultiplication)

  override def iPreprocess(f : IFormula, signature : Signature)
                        : (IFormula, Signature) =
    (Preprocessor.visit(f, ()).asInstanceOf[IFormula], signature)

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value)
                           : Boolean = true

  import IExpression._

  def int2ring(s: ITerm): ITerm =
    eps(ex((denom() === v(0)) & denomConstraint &
           (v(1) === ringMul(v(0), VariableShiftVisitor(s, 0, 2)))))

  def zero: ITerm = underlyingRing.zero
  def one : ITerm =
    eps((denom() === v(0)) & denomConstraint)

  def plus(s: ITerm, t: ITerm): ITerm =
    underlyingRing.plus(s, t)

  def mul (s: ITerm, t: ITerm): ITerm =
    // (s / denom) * (t / denom) =
    // s * t / denom^2 =
    // (s * t / denom) / denom
    eps(ex((denom() === v(0)) & denomConstraint &
           (ringMul(v(0), v(1)) ===
              ringMul(VariableShiftVisitor(s, 0, 2),
                      VariableShiftVisitor(t, 0, 2)))))

  override def times(num : IdealInt, s : ITerm) : ITerm =
    underlyingRing.times(num, s)

  def minus(s: ITerm): ITerm = underlyingRing.minus(s)

  private object Preprocessor extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`frac`, _) => {
        val Seq(num : ITerm, den : ITerm) = subres
        eps(ex(ex((denom() === v(0)) & denomConstraint &
                  (v(0) === ringMul(v(1), VariableShiftVisitor(den, 0, 3))) &
                  (v(2) === ringMul(v(1), VariableShiftVisitor(num, 0, 3))))))
      }
      case _ =>
        t update subres
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = name

}


object Rationals extends Fractions("Rat", IntegerRing, IExpression.v(0) > 0)

