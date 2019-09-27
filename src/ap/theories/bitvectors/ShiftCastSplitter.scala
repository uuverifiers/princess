/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2019 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

package ap.theories.bitvectors

import ap.theories._

import ap.theories.nia.IntervalPropagator
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula, TermOrder, OneTerm}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

/**
 * Splitter handles the splitting of l_shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object LShiftCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  protected[bitvectors] def shiftCastActions(goal : Goal, noSplits : Boolean)
                                           : Seq[Plugin.Action]={
    val castPreds =
      goal.facts.predConj.positiveLitsWithPred(_l_shift_cast).toBuffer

    Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

    val propagator = IntervalPropagator(goal)
      
    implicit val order = goal.order
    import TerForConvenience._

    // find simple l_shift_cast predicates that can be replaced by mod_cast
    var simpleElims : List[Plugin.Action] = List()
    
    var bestSplitNum = Int.MaxValue
    var splitPred : Option[(Atom,
                            IdealInt,  // lower exponent bound
                            IdealInt,  // upper exponent bound
                            Boolean,   // for upper bound all bits after shift
                                       // are zero
                            List[Formula])] = None

    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

    for (a <- castPreds) {
      var assumptions : List[Formula] = List(a)

      def addInEqAssumption(ineqs : Seq[Formula]) =
        for (f <- ineqs)
          assumptions = f :: assumptions

      if (a(2).isZero) {

        simpleElims =
          Plugin.RemoveFacts(a) ::
          Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order),
                          ModuloArithmetic) ::
          simpleElims

      } else if (a(3).isConstant) {

        simpleElims =
          Plugin.RemoveFacts(a) ::
          Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                            Array(a(0), a(1),
                                  a(2) * pow2(a(3).constant max IdealInt.ZERO),
                                  a(4)),
                            order),
                          ModuloArithmetic) ::
          simpleElims

      } else {

        val modulus = getModulus(a)
        val pow2Modulus = (modulus & (modulus - 1)).isZero

        val lBound =
          if (proofs)
            for ((b, assum) <-
                   propagator lowerBoundWithAssumptions a(3)) yield {
              // only non-negative bounds matter at this point!
              if (b.signum >= 0)
                addInEqAssumption(assum)
              b
            }
          else
            propagator lowerBound a(3)

        val (uBound, vanishing) =
          (propagator upperBound a(3)) match {
            case Some(ub)
              if (!pow2Modulus || ub < IdealInt(modulus.getHighestSetBit)) =>
                if (proofs) {
                  val Some((b, assum)) =
                    propagator upperBoundWithAssumptions a(3)
                  addInEqAssumption(assum)
                  (Some(b), false)
                } else {
                  (Some(ub), false)
                }
            case _ if pow2Modulus =>
              (Some(IdealInt(modulus.getHighestSetBit)), true)
            case _ =>
              (None, false)
          }

        (lBound, uBound) match {
          case (_, Some(upper)) if upper.signum <= 0 => {
            simpleElims =
              Plugin.RemoveFacts(a) ::
              Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                               Array(a(0), a(1), a(2), a(4)),
                               order),
                          ModuloArithmetic) ::
              simpleElims
          }
          case (Some(lower), Some(upper)) if lower >= upper => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, vanishing)
            //-END-ASSERTION-///////////////////////////////////////////////////

            // TRANSLATE TO BV_EXTRACT
            simpleElims =
              Plugin.RemoveFacts(a) ::
              Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                               Array(a(0), a(1),
                                     LinearCombination.ZERO, a(4)),
                               order),
                          ModuloArithmetic) ::
              simpleElims
          }
          case (rawLower, Some(upper)) if simpleElims.isEmpty => {
            // need to do some splitting
            val lower = rawLower getOrElse IdealInt.MINUS_ONE
            val cases = (upper - (lower max IdealInt.ZERO) + 1).intValueSafe
            if (cases < bestSplitNum) {
              bestSplitNum = cases
              splitPred = Some((a, lower, upper, vanishing, assumptions))
            }
          }
          case _ =>
            // nothing
        }

      }
    }

    if (!simpleElims.isEmpty) {

      simpleElims

    } else if (splitPred.isDefined) {

      if (noSplits)
        throw ModPlugin.NEEDS_SPLITTING

      val Some((a, lower, upper, vanishing, assumptions)) = splitPred

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, lower < upper && upper.signum >= 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val cases =
        (for (n <- IdealRange(lower max IdealInt.ZERO, upper + 1)) yield {
           if (n.isZero && lower < n) {
             (conj(List(a(3) <= n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), a(2), a(4)),
                             order))),
              List())
           } else if (vanishing && n == upper) {
             (conj(List(a(3) >= n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), LinearCombination.ZERO, a(4)),
                             order))),
              List())
           } else {
             (conj(List(a(3) === n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), a(2) * pow2(n), a(4)),
                             order))),
              List())
           }
         }).toBuffer

      List(Plugin.RemoveFacts(a),
           Plugin.AxiomSplit(assumptions,
                             cases.toList,
                             ModuloArithmetic))

    } else {

      List()

    }
  }

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println
      println("l_shift_cast splitter ...")
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    shiftCastActions(goal, false)
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Splitter handles the splitting of r_shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object RShiftCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  def isShiftInvariant(lc : LinearCombination) =
    lc.isConstant &&
    (lc.constant match {
       case IdealInt.ZERO => true
       case IdealInt.MINUS_ONE => true
       case _ => false
    })

  private def highestBit(v : IdealInt) : Int =
    v.signum match {
      case -1 =>
        if (v.isMinusOne)
          -1
        else
          (-v - 1).getHighestSetBit
      case 0 =>
        -1
      case 1 =>
        v.getHighestSetBit
    }

  import TerForConvenience._

  private def rshiftToExtract(a : Atom, shift : Int)
                             (implicit order : TermOrder) : Conjunction =
    (SortedPredicate argumentSorts a).last match {
      case UnsignedBVSort(bits) => {
        Atom(_bv_extract,
             Array(l(shift + bits - 1), l(shift), a(2), a(4)),
             order)
      }
      case _ => {
        // right-shift by dividing by 2^shift
        val factor = pow2(shift)
        val divRes = l(v(0))
        // factor * divRes <= a(2) && factor * divRes > a(2) - factor
        val lc1 = sum(List((IdealInt.ONE, a(2)), (-factor, divRes)))
        val lc2 = sum(List((IdealInt.MINUS_ONE, a(2)), 
                           (factor - 1, LinearCombination.ONE),
                           (factor, divRes)))
        val ineqs = geqZ(List(lc1, lc2))
        val matrix =
          ineqs & Atom(_mod_cast, Array(a(0), a(1), divRes, a(4)), order)
        exists(matrix)
      }
    }

  protected[bitvectors] def shiftCastActions(goal : Goal, noSplits : Boolean)
                                           : Seq[Plugin.Action] = {
    val castPreds =
      goal.facts.predConj.positiveLitsWithPred(_r_shift_cast).toBuffer

    Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

    val propagator = IntervalPropagator(goal)
      
    implicit val order = goal.order

    // find simple r_shift_cast predicates that can be replaced
    var simpleElims : List[Plugin.Action] = List()

    var bestSplitNum = Int.MaxValue
    var splitPred : Option[(Atom,
                            IdealInt,  // lower exponent bound
                            IdealInt,  // upper exponent bound
                            List[Formula])] = None

    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

    for (a <- castPreds) {
      var assumptions : List[Formula] = List(a)

      def addInEqAssumption(ineqs : Seq[Formula]) =
        for (f <- ineqs)
          assumptions = f :: assumptions

      // upper bound of the shift parameter
      val maybeShiftUpper =
        propagator upperBound a(3)

      // upper bound of shifts that have to be considered: for bigger
      // shifts the result will vanish, i.e., be either -1 or 0
      val mantUpper =
        for (b1 <- propagator lowerBound a(2);
             b2 <- propagator upperBound a(2)) yield {
          val m = highestBit(b1) max highestBit(b2)
          IdealInt(m + 1)
        }

      val (bounded, usingMantUpper, shiftUpper) =
        (maybeShiftUpper, mantUpper) match {
          case (None, None) =>
            (false, false, null)
          case (Some(b1), Some(b2)) =>
            if (b2 < b1)
              (true, true, b2)
            else
              (true, false, b1)
          case (Some(b), _) =>
            (true, false, b)
          case (_, Some(b)) =>
            (true, true, b)
        }

      if (bounded) {
        if (proofs) {
          if (usingMantUpper) {
            val Some((_, assum1)) = propagator lowerBoundWithAssumptions a(2)
            val Some((_, assum2)) = propagator upperBoundWithAssumptions a(2)
            addInEqAssumption(assum1)
            addInEqAssumption(assum2)
          } else {
            val Some((_, assum)) = propagator upperBoundWithAssumptions a(3)
            addInEqAssumption(assum)
          }
        }

        val shiftLower =
          (if (proofs)
             for ((b, assum) <- propagator lowerBoundWithAssumptions a(3);
                  if b.signum > 0) yield {
               addInEqAssumption(assum)
               b
             }
           else
             for (b <- propagator lowerBound a(3);
                  if b.signum > 0) yield {
               b
             }) getOrElse IdealInt.ZERO

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, shiftLower.signum >= 0)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        if (shiftLower >= shiftUpper) {

          simpleElims =
            Plugin.RemoveFacts(a) ::
            Plugin.AddAxiom(assumptions,
                            rshiftToExtract(a, shiftLower.intValueSafe),
                            ModuloArithmetic) ::
            simpleElims

        } else {

          val cases = (shiftUpper - shiftLower + 1).intValueSafe
          if (cases < bestSplitNum) {
            bestSplitNum = cases
            splitPred = Some((a, shiftLower, shiftUpper, assumptions))
          }

        }
      } else {
        println("WARNING: cannot handle unbounded shift " + a)
      }
    }

    if (!simpleElims.isEmpty) {

      simpleElims

    } else if (splitPred.isDefined) {

      if (noSplits)
        throw ModPlugin.NEEDS_SPLITTING

      val Some((a, lower, upper, assumptions)) = splitPred

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, lower < upper && lower.signum >= 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val cases =
        (for (n <- IdealRange(lower, upper + 1)) yield {
           (rshiftToExtract(a, n.intValueSafe) &
            (if (n == lower)
               a(3) <= lower
             else if (n == upper)
               a(3) >= upper
             else
               a(3) === n),
            List())
         }).toList

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug) {
        println("Splitting " + a + ":")
        for (a <- cases)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      List(Plugin.RemoveFacts(a),
           Plugin.AxiomSplit(assumptions, cases, ModuloArithmetic))

    } else {

      List()

    }
  }

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println
      println("r_shift_cast splitter ...")
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    shiftCastActions(goal, false)
  }
}
