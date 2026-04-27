/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2026 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

package ap.theories.bitvectors

import ap.theories._

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

import scala.collection.mutable.ArrayBuffer

/**
 * Splitter handles the splitting of l_shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object LShiftCastSplitHandler extends AtomSplitHandler {
  import ModuloArithmetic._

  val predicate = _l_shift_cast

  private val SPLIT_LIMIT = IdealInt(128)
  private val PRIORITY_FACTOR = 10

  private def analyseExpBounds(goal : Goal, a : Atom, proofs : Boolean)
                  : (IdealInt,          // lower exponent bound
                     Option[IdealInt],  // upper exponent bound
                     Boolean,           // for upper bound all bits after shift
                                        // are zero
                     List[Formula]) = {
    val propagator = goal.reduceWithFacts
    var assumptions : List[Formula] = List(a)

    def addInEqAssumption(ineqs : Seq[Formula]) =
      for (f <- ineqs)
        assumptions = f :: assumptions

    val modulus = getModulus(a)
    val pow2Modulus = (modulus & (modulus - 1)).isZero

    val lBound =
      if (proofs)
        for ((b, assum) <- propagator.lowerBound(a(3), true)) yield {
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
              val Some((b, assum)) = propagator.upperBound(a(3), true)
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

    (lBound.getOrElse(IdealInt.MINUS_ONE), uBound, vanishing, assumptions)
  }

  def applicationPriority(goal : Goal, args : ApplicationPoint) : Int = {
    val order = goal.order
    val a = Atom(_l_shift_cast, args, order)
    analyseExpBounds(goal, a, false) match {
      case (lower, Some(upper), _, _) =>
        ((upper - (lower max IdealInt.ZERO) + 1) min SPLIT_LIMIT
          ).intValueSafe * PRIORITY_FACTOR
      case _ =>
        SPLIT_LIMIT.intValueSafe * PRIORITY_FACTOR
    }
  }

  def handleApplicationPoint(goal : Goal,
                             args : ApplicationPoint) : Seq[Plugin.Action] = {
    implicit val order : TermOrder = goal.order
    import TerForConvenience._

    val a = Atom(_l_shift_cast, args, order)

    if (goal.facts.predConj.positiveLitsAsSet.contains(a)) {
      val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last
      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      val actions = new ArrayBuffer[Plugin.Action]

      analyseExpBounds(goal, a, proofs) match {
        case (_, Some(expUB), _, assumptions) if expUB.signum <= 0 => {
          // TODO: handle this case in ModReducer?
          actions += Plugin.RemoveFacts(a)
          actions += Plugin.AddAxiom(assumptions.distinct,
                                     Atom(_mod_cast,
                                          Array(a(0), a(1), a(2), a(4)),
                                     order),
                                     ModuloArithmetic)
        }

        case (expLB, Some(expUB), vanishing, assumptions)
            if expUB - (expLB max IdealInt.ZERO) + 1 <= SPLIT_LIMIT => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, expLB < expUB && expUB.signum >= 0)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          actions += Plugin.RemoveFacts(a)

          val cases =
            (for (n <- IdealRange(expLB max IdealInt.ZERO, expUB + 1)) yield {
              if (n.isZero && expLB < n) {
                (conj(List(a(3) <= n,
                            Atom(_mod_cast,
                                 Array(a(0), a(1), a(2), a(4)),
                                 order))),
                  List())
              } else if (vanishing && n == expUB) {
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
            }).toList

          actions += Plugin.AxiomSplit(assumptions.distinct,
                                        cases,
                                        ModuloArithmetic)
        }

        case (expLB, _, _, assumptions) => {
          val ub = (expLB max IdealInt.ZERO) + SPLIT_LIMIT
          val cases =
            (for (n <- IdealRange(expLB max IdealInt.ZERO, ub + 1)) yield {
              if (n.isZero && expLB < n) {
                (conj(List(a(3) <= n,
                            Atom(_mod_cast,
                                 Array(a(0), a(1), a(2), a(4)),
                                 order))),
                 List(Plugin.RemoveFacts(a)))
              } else if (n == ub) {
                (conj(List(a(3) >= n)),
                 List())
              } else {
                (conj(List(a(3) === n,
                            Atom(_mod_cast,
                                 Array(a(0), a(1), a(2) * pow2(n), a(4)),
                                 order))),
                 List(Plugin.RemoveFacts(a)))
              }
            }).toList

          actions += Plugin.AxiomSplit(assumptions.distinct,
                                       cases,
                                       ModuloArithmetic)
        }
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug && !actions.isEmpty) {
        println("l-shift-cast splitting:")
        for (a <- actions)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions.toSeq
    } else {
      List()
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Splitter handles the splitting of r_shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object RShiftCastSplitHandler extends AtomSplitHandler {
  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  val predicate = _r_shift_cast

  private val SPLIT_LIMIT = IdealInt(128)
  private val PRIORITY_FACTOR = 10

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

  private def analyseBounds(goal : Goal, a : Atom, proofs : Boolean)
                  : (IdealInt,         // lower shift bound
                     Option[IdealInt], // upper shift bound
                     List[Formula]) = {
    val propagator = goal.reduceWithFacts
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
          (false, false, None)
        case (Some(b1), Some(b2)) =>
          if (b2 < b1)
            (true, true, Some(b2))
          else
            (true, false, Some(b1))
        case (Some(b), _) =>
          (true, false, Some(b))
        case (_, Some(b)) =>
          (true, true, Some(b))
      }

    val shiftLower =
      (if (proofs)
          for ((b, assum) <- propagator.lowerBound(a(3), true);
              if b.signum > 0) yield {
            addInEqAssumption(assum)
            b
          }
        else
          for (b <- propagator lowerBound a(3);
                if b.signum > 0) yield {
            b
          }) getOrElse IdealInt.ZERO

      if (bounded && proofs) {
        if (usingMantUpper) {
          val Some((_, assum1)) = propagator.lowerBound(a(2), true)
          val Some((_, assum2)) = propagator.upperBound(a(2), true)
          addInEqAssumption(assum1)
          addInEqAssumption(assum2)
        } else {
          val Some((_, assum)) = propagator.upperBound(a(3), true)
          addInEqAssumption(assum)
        }
      }

    (shiftLower, shiftUpper, assumptions)
  }

  def applicationPriority(goal : Goal, args : ApplicationPoint) : Int = {
    val order = goal.order
    val a = Atom(_r_shift_cast, args, order)
    analyseBounds(goal, a, false) match {
      case (lower, Some(upper), _) =>
        if (lower >= upper)
          0
        else
          ((upper - lower + 1) min SPLIT_LIMIT).intValueSafe * PRIORITY_FACTOR
      case _ =>
        SPLIT_LIMIT.intValueSafe * PRIORITY_FACTOR
    }
  }

  private def rshiftToExtract(a : Atom, shift : IdealInt)
                             (implicit order : TermOrder) : Conjunction = {
    import TerForConvenience._
    (SortedPredicate argumentSorts a).last match {
      case UnsignedBVSort(bits) => {
        Atom(_bv_extract,
             Array(l(shift + bits - 1), l(shift), a(2), a(4)),
             order)
      }
      case SignedBVSort(bits) if shift > bits =>
        // TODO: this is only correct if the argument a(2) is also of sort
        // SignedBVSort(bits), which we cannot assume at this point. Need to
        // check the bounds of a(2)!
        rshiftToExtract(a, bits)
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
  }

  def handleApplicationPoint(goal : Goal,
                             args : ApplicationPoint) : Seq[Plugin.Action] = {
    implicit val order : TermOrder = goal.order
    import TerForConvenience._

    val a = Atom(_r_shift_cast, args, order)

    if (goal.facts.predConj.positiveLitsAsSet.contains(a)) {
      val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last
      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      val actions = new ArrayBuffer[Plugin.Action]

      analyseBounds(goal, a, proofs) match {

        case (shiftLower, Some(shiftUpper), assumptions)
            if shiftLower >= shiftUpper => {
          // Only a single case; handle in reducer?
          actions += Plugin.RemoveFacts(a)
          actions += Plugin.AddAxiom(assumptions.distinct,
                                     rshiftToExtract(a, shiftLower),
                                     ModuloArithmetic)
        }

        case (shiftLower, maybeShiftUpper, assumptions) => {
          val effectiveUpper = maybeShiftUpper match {
            case Some(upper) if upper <= shiftLower + SPLIT_LIMIT =>
              upper
            case _ =>
              shiftLower + SPLIT_LIMIT
          }

          val canElim =
            maybeShiftUpper == Some(effectiveUpper)

          val cases =
            (for (n <- IdealRange(shiftLower, effectiveUpper + 1)) yield {
              (rshiftToExtract(a, n) &
              (if (n == shiftLower)
                  a(3) <= shiftLower
                else if (n == effectiveUpper)
                  a(3) >= effectiveUpper
                else
                  a(3) === n),
              List())
            }).toList

          if (canElim)
            actions += Plugin.RemoveFacts(a)

          actions += Plugin.AxiomSplit(assumptions.distinct,
                                       cases,
                                       ModuloArithmetic)
        }
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug && !actions.isEmpty) {
        println("r-shift-cast splitting:")
        for (a <- actions)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions.toSeq
    } else {
      List()
    }
  }
}

/**
 * Splitter handles the splitting of r_shift_cast-operations, when no other
 * inference steps are possible anymore.
 */
object RShiftCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

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

  private def rshiftToExtract(a : Atom, shift : IdealInt)
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

    val propagator = goal.reduceWithFacts
      
    implicit val order = goal.order

    // find simple r_shift_cast predicates that can be replaced
    var simpleElims : List[Plugin.Action] = List()

    var bestSplitNum = Int.MaxValue
    var splitPred : Option[(Atom,
                            IdealInt,  // lower exponent bound
                            IdealInt,  // upper exponent bound
                            List[Formula])] = None

    def addSplitOption(
          cases : IdealInt,
          pred : (Atom, IdealInt, IdealInt, List[Formula])) : Unit =
      cases match {
        case IdealInt(cases) if cases < bestSplitNum => {
          bestSplitNum = cases
          splitPred = Some(pred)
        }
        case _ if bestSplitNum == Int.MaxValue => {
          splitPred = Some(pred)
        }
        case _ => // nothing
      }

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

      val shiftLower =
        (if (proofs)
           for ((b, assum) <- propagator.lowerBound(a(3), true);
                if b.signum > 0) yield {
             addInEqAssumption(assum)
             b
           }
         else
           for (b <- propagator lowerBound a(3);
                 if b.signum > 0) yield {
             b
           }) getOrElse IdealInt.ZERO

      if (bounded) {
        if (proofs) {
          if (usingMantUpper) {
            val Some((_, assum1)) = propagator.lowerBound(a(2), true)
            val Some((_, assum2)) = propagator.upperBound(a(2), true)
            addInEqAssumption(assum1)
            addInEqAssumption(assum2)
          } else {
            val Some((_, assum)) = propagator.upperBound(a(3), true)
            addInEqAssumption(assum)
          }
        }

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, shiftLower.signum >= 0)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        if (shiftLower >= shiftUpper) {

          simpleElims =
            Plugin.RemoveFacts(a) ::
            Plugin.AddAxiom(assumptions.distinct,
                            rshiftToExtract(a, shiftLower),
                            ModuloArithmetic) ::
            simpleElims

        } else {

          addSplitOption(shiftUpper - shiftLower + 1,
                         (a, shiftLower, shiftUpper, assumptions))

        }
      } else {
        println("WARNING: unbounded shift " + a)

        addSplitOption(Int.MaxValue,
                       (a, shiftLower, null, assumptions))

      }
    }

    if (!simpleElims.isEmpty) {

      simpleElims

    } else if (splitPred.isDefined) {

      if (noSplits)
        throw ModPlugin.NEEDS_SPLITTING

      val Some((a, lower, upper, assumptions)) = splitPred

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, lower.signum >= 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val cases = upper match {
        case null => {
          // an unbounded shift predicate; in this case we just apply
          // binary splitting

          List(
            (rshiftToExtract(a, lower) & (a(3) <= lower), List()),
            (conj(a(3) > lower), List())
          )
        }

        case upper => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, lower < upper)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          (for (n <- IdealRange(lower, upper + 1)) yield {
             (rshiftToExtract(a, n) &
             (if (n == lower)
                a(3) <= lower
              else if (n == upper)
                a(3) >= upper
              else
                a(3) === n),
             List())
          }).toList
        }
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug) {
        println("Splitting " + a + ":")
        for (a <- cases)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      List(Plugin.RemoveFacts(a),
           Plugin.AxiomSplit(assumptions.distinct, cases, ModuloArithmetic))

    } else {

      List()

    }
  }

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println()
      println("r_shift_cast splitter ...")
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    shiftCastActions(goal, false)
  }
}
