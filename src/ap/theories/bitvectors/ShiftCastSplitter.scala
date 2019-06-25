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

import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

/**
 * Splitter handles the splitting of shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object ShiftCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  protected[bitvectors] def shiftCastActions(goal : Goal) : Seq[Plugin.Action]={
    val castPreds =
      goal.facts.predConj.positiveLitsWithPred(_l_shift_cast).toBuffer

    Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

    val reducer = goal.reduceWithFacts
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

      def addInEqAssumption(ineqs : Seq[LinearCombination]) =
        for (lc <- ineqs)
          assumptions = InEqConj(lc, order) :: assumptions

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
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(3)) yield {
              // only non-negative bounds matter at this point!
              if (b.signum >= 0)
                addInEqAssumption(assum)
              b
            }
          else
            reducer lowerBound a(3)

        val (uBound, vanishing) =
          (reducer upperBound a(3)) match {
            case Some(ub)
              if (!pow2Modulus || ub < IdealInt(modulus.getHighestSetBit)) =>
                if (proofs) {
                  val Some((b, assum)) = reducer upperBoundWithAssumptions a(3)
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
//println("shift splitter " + goal.facts)
    shiftCastActions(goal)
  }
}
