/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.parameters.Param
import ap.terfor.{TerForConvenience, Formula, Term, TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import ap.types.SortedPredicate
import LinearCombination.Constant
import ap.util.Debug

import scala.collection.mutable.{LinkedHashMap, HashSet => MHashSet,
                                 HashMap => MHashMap, ArrayBuffer}

/**
 * ModCastIntervalPropagator handles interval constraint propagation
 * between the arguments and results of mod_cast atoms.
 */
object ModCastIntervalPropagator {

  import ModuloArithmetic._

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    if (goal.facts.predConj.predicates.contains(_mod_cast)) {
      bwdPropagation(goal)
    } else {
      List()
    }

  /**
   * Propagate information about mod_cast results to the mod_cast arguments.
   */
  def bwdPropagation(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order : TermOrder = goal.order

    val casts    = goal.facts.predConj.positiveLitsWithPred(_mod_cast)
    val reducer  = goal.reduceWithFacts
    val proofs   = Param.PROOF_CONSTRUCTION(goal.settings)
    import reducer.{lowerBound, upperBound}

    val actions  = new ArrayBuffer[Plugin.Action]

    for (a <- casts) {
      val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last
      import sort.modulus

      (lowerBound(a(3), proofs), upperBound(a(3), proofs)) match {
        case (Some((resLB, resLBAsses)), Some((resUB, resUBAsses)))
            if resLB > sortLB || resUB < sortUB =>{

          // check whether a lower bound on the mod_cast argument can be
          // improved
          for ((argLB, argLBAsses) <- lowerBound(a(2), proofs);
               lowerFactor = (argLB - sortLB) / modulus;
               if resUB < argLB - lowerFactor * modulus) {
            val newArgLB = resLB + (lowerFactor + 1) * modulus
            if (newArgLB > argLB) {
//              println(s"Improved lower bound: $argLB -> $newArgLB for $a")
              val action =
                Plugin.AddAxiom(resLBAsses ++ resUBAsses ++ argLBAsses ++
                                  List(a),
                                a(2) >= newArgLB,
                                ModuloArithmetic)
              //-BEGIN-ASSERTION-///////////////////////////////////////////
              if (debug) {
                println(s"Inferred new lower bound $newArgLB for term ${a(2)}:")
                println("\t" + action)
              }
              //-END-ASSERTION-/////////////////////////////////////////////
              actions += action
            }
          }
        }

        // check whether a lower bound on the mod_cast argument can be
        // improved
        for ((argUB, argUBAsses) <- upperBound(a(2), proofs);
             upperFactor = -((sortUB - argUB) / modulus);
             if resLB > argUB - upperFactor * modulus) {
          val newArgUB = resUB + (upperFactor - 1) * modulus
          if (newArgUB < argUB) {
//            println(s"Improved upper bound: $argUB -> $newArgUB for $a")
            val action =
              Plugin.AddAxiom(resLBAsses ++ resUBAsses ++ argUBAsses ++
                                List(a),
                              a(2) <= newArgUB,
                              ModuloArithmetic)
            //-BEGIN-ASSERTION-///////////////////////////////////////////////
            if (debug) {
              println(s"Inferred new upper bound $newArgUB for term ${a(2)}:")
              println("\t" + action)
            }
            //-END-ASSERTION-/////////////////////////////////////////////////
            actions += action
          }
        }

        case _ => // nothing
      }
    }

    actions.toSeq
  }
}
