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

import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula, Term, TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import LinearCombination.Constant
import ap.util.Debug

import scala.collection.mutable.{LinkedHashMap, HashSet => MHashSet,
                                 HashMap => MHashMap, ArrayBuffer}

/**
 * ExtractIntervalPropagator handles interval constraint propagation
 * between the arguments and results of extract atoms.
 */
object ExtractIntervalPropagator {

  import ModuloArithmetic._

    def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      import TerForConvenience._
      implicit val order : TermOrder = goal.order

      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
      if (extracts.isEmpty)
        return List()

      val inEqs = goal.facts.arithConj.inEqs
      val reducer = goal.reduceWithFacts

      val actions = new ArrayBuffer[Plugin.Action]

      // TODO: make sure that the order of actions is deterministic
      // TODO: add optimized version when no proofs are generated
      for ((arg, exes) <- extracts.groupBy(_(2))) {
        reducer.lowerBoundWithAssumptions(arg) match {
          case Some((argLB, argLBAssumptions)) => {
            // check whether we can derive a tighter lower bound based on the
            // bounds on extracts
            val allAssumptions = new ArrayBuffer[Formula]
            allAssumptions ++= argLBAssumptions.map(_ >= 0)

            val Atom(_, Seq(Constant(IdealInt(headU)), _, _, _), _) = exes.head

            var lastL = headU + 1
            var newArgLB = argLB / pow2(lastL) * pow2(lastL)

            for (ex@Atom(_, Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
                                _, res), _) <- exes.iterator;
                 if ub < lastL) {
              reducer.lowerBoundWithAssumptions(res) match {
                case Some((resLB, resLBAssumptions)) if resLB.signum > 0 => {
                  newArgLB = newArgLB + resLB * pow2(lb)
                  allAssumptions ++= resLBAssumptions.map(_ >= 0)
                  allAssumptions += ex
                }
                case _ =>
              }
              lastL = lb
            }

            if (newArgLB > argLB) {
              val action = Plugin.AddAxiom(allAssumptions, arg >= newArgLB,
                                           ModuloArithmetic)
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              if (debug) {
                println(s"Inferred new lower bound $newArgLB for term $arg:")
                println("\t" + action)
              }
              //-END-ASSERTION-/////////////////////////////////////////////////
              actions += action
            }
          }

          case None => // without an initial lower bound, nothing can be done
        }

        reducer.upperBoundWithAssumptions(arg) match {
          case Some((argUB, argUBAssumptions)) => {
            // check whether we can derive a tighter upper bound based on the
            // bounds on extracts
            val allAssumptions = new ArrayBuffer[Formula]
            allAssumptions ++= argUBAssumptions.map(_ >= 0)

            val Atom(_, Seq(Constant(IdealInt(headU)), _, _, _), _) = exes.head

            var lastL = headU + 1
            var newArgUB = (argUB / pow2(lastL) + 1) * pow2(lastL) - 1

            for (ex@Atom(_, Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
                                _, res), _) <- exes.iterator;
                 if ub < lastL) {
              reducer.upperBoundWithAssumptions(res) match {
                case Some((resUB, resUBAssumptions))
                    if resUB < pow2MinusOne(ub - lb + 1) => {
                  newArgUB =
                    newArgUB - (pow2MinusOne(ub - lb + 1) - resUB) * pow2(lb)
                  allAssumptions ++= resUBAssumptions.map(_ >= 0)
                  allAssumptions += ex
                }
                case _ =>
              }
              lastL = lb
            }

            if (newArgUB < argUB) {
              val action = Plugin.AddAxiom(allAssumptions, arg <= newArgUB,
                                           ModuloArithmetic)
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              if (debug) {
                println(s"Inferred new upper bound $newArgUB for term $arg:")
                println("\t" + action)
              }
              //-END-ASSERTION-/////////////////////////////////////////////////
              actions += action
            }
          }

          case None => // without an initial lower bound, nothing can be done
        }
      }

      actions.toSeq
    }

}