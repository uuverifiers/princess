/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.parameters.Param
import ap.terfor.{TerForConvenience, Formula, Term, TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction
import LinearCombination.Constant
import ap.util.Debug

import scala.collection.mutable.{LinkedHashMap, HashSet => MHashSet,
                                 HashMap => MHashMap, ArrayBuffer}

/**
 * BitwiseOpIntervalPropagator handles interval constraint propagation
 * between the arguments and results of bit-wise operators, currently bv_and.
 */
object BitwiseOpIntervalPropagator {
  import ModuloArithmetic._

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    fwdAndPropagation(goal) ++ fwdXorPropagation(goal)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Propagate information about arguments to the result.
   */
  def fwdAndPropagation(goal : Goal) : Seq[Plugin.Action] = {
    if (!goal.facts.predConj.predicates.contains(_bv_and))
      return List()

    import TerForConvenience._
    implicit val order : TermOrder = goal.order

    val bvops    = goal.facts.predConj.positiveLitsWithPred(_bv_and)
    val reducer  = goal.reduceWithFacts
    val proofs   = Param.PROOF_CONSTRUCTION(goal.settings)
    import reducer.{lowerBound, upperBound}

    val actions  = new ArrayBuffer[Plugin.Action]

    for (atom@Atom(`_bv_and`, Seq(Constant(bits), arg1, arg2, res), _) <-
           bvops) {
      val domSize = pow2MinusOne(bits)
      val arg1UBound = upperBound(arg1, proofs)
      val arg2UBound = upperBound(arg2, proofs)

      // Derive upper bounds
      val (uBound, uAssumptions) =
        (arg1UBound, arg2UBound) match {
          case (Some(p1@(arg1UB, _)), Some(p2@(arg2UB, _))) =>
            if (arg1UB <= arg2UB) p1 else p2
          case (Some(p1), _) =>
            p1
          case (_, Some(p2)) =>
            p2
          case _ =>
            (domSize, List())
      }

      val ubIneq = res <= uBound
      if (!reducer(ubIneq).isTrue) {
        val action =
          Plugin.AddAxiom(uAssumptions ++ List(atom), ubIneq, ModuloArithmetic)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println(s"Inferred new upper bound $uBound for term $res")
          println("\t" + action)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        actions += action
      }

      // Derive lower bounds
      val arg1LBound = lowerBound(arg1, proofs)
      val arg2LBound = lowerBound(arg2, proofs)

      val arg1BitsLB =
        for ((lb, assumptions1) <- arg1LBound;
             (ub, assumptions2) <- arg1UBound;
             b <- commonBitsLB(lb, ub))
        yield (b, assumptions1 ++ assumptions2)
      val arg2BitsLB =
        for ((lb, assumptions1) <- arg2LBound;
             (ub, assumptions2) <- arg2UBound;
             b <- commonBitsLB(lb, ub))
        yield (b, assumptions1 ++ assumptions2)

      val (lBound, lAssumptions) =
        (arg1BitsLB, arg2BitsLB) match {
          case (Some((b1, asses1)), Some((b2, asses2))) => {
            val fixedBits1 = ((arg1LBound.get._1 >> b1) << b1) & domSize
            val fixedBits2 = ((arg2LBound.get._1 >> b2) << b2) & domSize
            val fixedBits = fixedBits1 & fixedBits2
            (fixedBits, asses1 ++ asses2)
          }
          case _ =>
           // no useful bound
           (IdealInt.ZERO, List())
        }

      val lbIneq = res >= lBound
      if (!reducer(lbIneq).isTrue) {
        val action =
          Plugin.AddAxiom(lAssumptions ++ List(atom), lbIneq, ModuloArithmetic)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println(s"Inferred new lower bound $lBound for term $res")
          println("\t" + action)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        actions += action
      }
    }

    actions.toSeq
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Propagate information about arguments to the result.
   */
  def fwdXorPropagation(goal : Goal) : Seq[Plugin.Action] = {
    if (!goal.facts.predConj.predicates.contains(_bv_xor))
      return List()

    import TerForConvenience._
    implicit val order : TermOrder = goal.order

    val bvops    = goal.facts.predConj.positiveLitsWithPred(_bv_xor)
    val reducer  = goal.reduceWithFacts
    val proofs   = Param.PROOF_CONSTRUCTION(goal.settings)
    import reducer.{lowerBound, upperBound}

    val actions  = new ArrayBuffer[Plugin.Action]

    for (atom@Atom(`_bv_xor`, Seq(Constant(bits), arg1, arg2, res), _) <-
           bvops) {
      val arg1UBound = upperBound(arg1, proofs)
      val arg2UBound = upperBound(arg2, proofs)
      val arg1LBound = lowerBound(arg1, proofs)
      val arg2LBound = lowerBound(arg2, proofs)

      val arg1BitsLB =
        for ((lb, assumptions1) <- arg1LBound;
             (ub, assumptions2) <- arg1UBound;
             b <- commonBitsLB(lb, ub))
        yield (b, assumptions1 ++ assumptions2)
      val arg2BitsLB =
        for ((lb, assumptions1) <- arg2LBound;
             (ub, assumptions2) <- arg2UBound;
             b <- commonBitsLB(lb, ub))
        yield (b, assumptions1 ++ assumptions2)

      val (bounds, assumptions) =
        (arg1BitsLB, arg2BitsLB) match {
          case (Some((b1, asses1)), Some((b2, asses2))) => {
            val domSize = pow2MinusOne(bits)
            val b = b1 max b2
            val fixedBits1 = ((arg1LBound.get._1 >> b) << b) & domSize
            val fixedBits2 = ((arg2LBound.get._1 >> b) << b) & domSize
            val fixedBits = fixedBits1 ^ fixedBits2
            ((res >= fixedBits) & (res <= fixedBits + pow2MinusOne(b)),
             asses1 ++ asses2)
          }
          case _ =>
           // no useful bound
           (Conjunction.TRUE, List())
        }

      if (!reducer(bounds).isTrue) {
        val action =
          Plugin.AddAxiom(assumptions ++ List(atom), bounds, ModuloArithmetic)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println(s"Inferred new bounds for term $res")
          println("\t" + action)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        actions += action
      }
    }

    actions.toSeq
  }
}