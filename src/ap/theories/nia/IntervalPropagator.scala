/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2019 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.theories.nia

import ap.basetypes.IdealInt
import ap.proof.goal.Goal
import ap.terfor.{ConstantTerm, Formula, Term, OneTerm, VariableTerm}
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.util.Seqs

import scala.collection.immutable.BitSet
import scala.collection.mutable.ArrayBuffer

object IntervalPropagator {
  def apply(goal : Goal,
            ordering : MonomialOrdering,
            simplifiedGB : Basis) : IntervalPropagator =
    new IntervalPropagator(goal, ordering, simplifiedGB, false)

  def apply(goal : Goal) : IntervalPropagator = {
    val order = new GrevlexOrdering(goal.order.constOrdering)
    new IntervalPropagator(goal, order, null, true)
  }
}

/**
 * Simple class to derive interval bounds for the constants in a
 * proof goal
 */
class IntervalPropagator private (goal : Goal,
                                  ordering : MonomialOrdering,
                                  simplifiedGB : Basis,         // might be null
                                  compatibleOrder : Boolean) {

  import GroebnerMultiplication._mul
  import Seqs.{optionMax, optionMin}

  private implicit val _ = ordering
  private val order      = goal.order

  private def fromLinearCombination(lc : LinearCombination) =
    if (compatibleOrder)
      Polynomial fromLinearCombination lc
    else
      Polynomial fromLinearCombinationGen lc

  private def fromMulAtom(a : Atom) =
    if (compatibleOrder)
      Polynomial fromMulAtom a
    else
      Polynomial fromMulAtomGen a

  private val reducer = goal.reduceWithFacts

  private val mulPredicates =
    goal.facts.predConj.positiveLitsWithPred(_mul)

  private val inequalities   = goal.facts.arithConj.inEqs
  private val disequalities  = goal.facts.arithConj.negativeEqs
  private val ineqOffset     = mulPredicates.size
  private val ineqInfsOffset = ineqOffset + inequalities.size
  private val negeqOffset    = ineqInfsOffset + inequalities.geqZeroInfs.size

  private def label2Assum(l : BitSet) : Seq[Formula] =
    for (ind <- l.toSeq) yield {
      if (ind < ineqOffset)
        mulPredicates(ind)
      else if (ind < ineqInfsOffset)
        InEqConj(inequalities(ind - ineqOffset), order)
      else if (ind < negeqOffset)
        InEqConj(inequalities.geqZeroInfs(ind - ineqInfsOffset), order)
      else
        NegEquationConj(disequalities(ind - negeqOffset), order)
    }

  private val preds =
    ((for ((a, n) <- mulPredicates.iterator.zipWithIndex;
           poly = fromMulAtom(a);
           if !poly.isZero)
      yield (poly, BitSet(n))) ++
     (if (simplifiedGB == null)
        Iterator.empty
      else
        (for (p <- simplifiedGB.polyIterator)
         yield (p, simplifiedGB labelFor p)))).toArray

  private val ineqs =
    ((for ((lc, n) <- inequalities.iterator.zipWithIndex;
           if lc.constants.size > 1)
      yield (fromLinearCombination(lc), BitSet(n + ineqOffset))) ++
     // For square predicates t*t = s, add an inequality s >= 0
     (for ((a, n) <- mulPredicates.iterator.zipWithIndex;
           if a(0) == a(1))
      yield (fromLinearCombination(a(2)), BitSet(n)))).toArray

  private val negeqs =
    (for ((lc, n) <- goal.facts.arithConj.negativeEqs.iterator.zipWithIndex)
     yield (fromLinearCombination(lc), BitSet(n + negeqOffset))).toArray

  val intervalSet : Option[IntervalSet] =
    if (preds.isEmpty && ineqs.isEmpty && negeqs.isEmpty) {
      // if there are only basic bounds, don't even construct the IntervalSet
      None
    } else {
      val basicBounds =
        ((for ((lc, n) <- inequalities.iterator.zipWithIndex;
               if lc.constants.size == 1)
          yield (lc, BitSet(n + ineqOffset))) ++
         (for ((lc, n) <- inequalities.geqZeroInfs.iterator.zipWithIndex;
               if lc.constants.size == 1)
          yield (lc, BitSet(n + ineqInfsOffset)))).toArray

      Some(new IntervalSet(preds, ineqs, negeqs, basicBounds))
    }

  //////////////////////////////////////////////////////////////////////////////

  def lowerBound(t : Term) : Option[IdealInt] = t match {
    case OneTerm => Some(IdealInt.ONE)
    case c : ConstantTerm => lowerBound(c)
    case lc : LinearCombination => lowerBound(lc)
    case _ : VariableTerm =>
      throw new IllegalArgumentException
  }

  def upperBound(t : Term) : Option[IdealInt] = t match {
    case OneTerm => Some(IdealInt.ONE)
    case c : ConstantTerm => upperBound(c)
    case lc : LinearCombination => upperBound(lc)
    case _ : VariableTerm =>
      throw new IllegalArgumentException
  }

  def lowerBound(lc : LinearCombination) : Option[IdealInt] =
    linCompBound(lc, false)

  def upperBound(lc : LinearCombination) : Option[IdealInt] =
    linCompBound(lc, true)

  def lowerBound(c : ConstantTerm) : Option[IdealInt] = {
    val b1 = for (set <- intervalSet;
                  iv <- set getTermIntervalOption c;
                  if iv.lower.isInstanceOf[IntervalVal])
             yield iv.lower.get
    val b2 = reducer lowerBound c
    (b1, b2) match {
      case (Some(b1), Some(b2)) =>
        Some(b1 max b2)
      case (r@Some(_), None) =>
        r
      case (None, r@Some(_)) =>
        r
      case (None, None) =>
        None
    }
  }

  def upperBound(c : ConstantTerm) : Option[IdealInt] = {
    val b1 = for (set <- intervalSet;
                  iv <- set getTermIntervalOption c;
                  if iv.upper.isInstanceOf[IntervalVal])
             yield iv.upper.get
    val b2 = reducer upperBound c
    (b1, b2) match {
      case (Some(b1), Some(b2)) =>
        Some(b1 min b2)
      case (r@Some(_), None) =>
        r
      case (None, r@Some(_)) =>
        r
      case (None, None) =>
        None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def lowerBoundWithAssumptions(t : Term)
                   : Option[(IdealInt, Seq[Formula])] = t match {
    case OneTerm =>
      Some((IdealInt.ONE, List()))
    case c : ConstantTerm =>
      lowerBoundWithAssumptions(c)
    case t : LinearCombination =>
      linCompBoundWithAssumptions(t, false)
    case _ : VariableTerm =>
      throw new IllegalArgumentException
  }

  def upperBoundWithAssumptions(t : Term)
                   : Option[(IdealInt, Seq[Formula])] = t match {
    case OneTerm =>
      Some((IdealInt.ONE, List()))
    case c : ConstantTerm =>
      upperBoundWithAssumptions(c)
    case t : LinearCombination =>
      linCompBoundWithAssumptions(t, true)
    case _ : VariableTerm =>
      throw new IllegalArgumentException
  }

  def lowerBoundWithAssumptions(c : ConstantTerm)
                              : Option[(IdealInt, Seq[Formula])] = {
    val b1 = for (set <- intervalSet;
                  iv <- set getTermIntervalOption c;
                  if iv.lower.isInstanceOf[IntervalVal])
             yield iv.lower.get
    val b2 = reducer lowerBound c
    (b1, b2) match {
      case (Some(b), None) =>
        Some((b, label2Assum((intervalSet.get getLabelledTermInterval c)._2._1)))
      case (Some(b), Some(b2)) if b > b2 =>
        Some((b, label2Assum((intervalSet.get getLabelledTermInterval c)._2._1)))
      case (_, Some(_)) => {
        val Some((b, assumptions)) = reducer lowerBoundWithAssumptions c
        Some((b, for (lc <- assumptions) yield InEqConj(lc, order)))
      }
      case (None, None) =>
        None
    }
  }

  def upperBoundWithAssumptions(c : ConstantTerm)
                              : Option[(IdealInt, Seq[Formula])] = {
    val b1 = for (set <- intervalSet;
                  iv <- set getTermIntervalOption c;
                  if iv.upper.isInstanceOf[IntervalVal])
             yield iv.upper.get
    val b2 = reducer upperBound c

    (b1, b2) match {
      case (Some(b), None) =>
        Some((b, label2Assum((intervalSet.get getLabelledTermInterval c)._2._2)))
      case (Some(b), Some(b2)) if b < b2 =>
        Some((b, label2Assum((intervalSet.get getLabelledTermInterval c)._2._2)))
      case (_, Some(_)) => {
        val Some((b, assumptions)) = reducer upperBoundWithAssumptions c
        Some((b, for (lc <- assumptions) yield InEqConj(lc, order)))
      }
      case (None, None) =>
        None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def linCompBound(t : LinearCombination,
                           upper : Boolean) : Option[IdealInt] = {
    var bound = IdealInt.ZERO
    var i = 0
    while (i < t.lcSize && bound != null) {
      bound = coeffBound(t getCoeff i, t getTerm i, bound, upper)
      i = i + 1        
    }
    Option(bound)
  }

  private def linCompBoundWithAssumptions(t : LinearCombination,
                                          upper : Boolean)
                                        : Option[(IdealInt, Seq[Formula])] = {
    var bound = IdealInt.ZERO
    var assumptions = new ArrayBuffer[Formula]
    var i = 0
    while (i < t.lcSize && bound != null) {
      val p = coeffBoundWithAssumptions(t getCoeff i, t getTerm i, bound, upper)
      if (p == null) {
        bound = null
      } else {
        bound = p._1
        assumptions ++= p._2
      }
      i = i + 1
    }
    if (bound == null)
      None
    else
      Some((bound, assumptions.toIndexedSeq))
  }

  /**
   * Returns null if there is no bound.
   */
  private def coeffBound(coeff : IdealInt, term : Term,
                         offset : IdealInt, upper : Boolean) : IdealInt =
    (if ((coeff.signum > 0) != upper)
       lowerBound(term)
     else
       upperBound(term)) match {
      case Some(b) => b * coeff + offset
      case None => null
    }

  /**
   * Returns null if there is no bound.
   */
  private def coeffBoundWithAssumptions
                   (coeff : IdealInt, term : Term,
                    offset : IdealInt, upper : Boolean)
                   : (IdealInt, Seq[Formula]) =
    (if ((coeff.signum > 0) != upper)
       lowerBoundWithAssumptions(term)
     else
       upperBoundWithAssumptions(term)) match {
      case Some((b, assumptions)) =>
        (b * coeff + offset, assumptions)
      case None =>
        null
    }

}
