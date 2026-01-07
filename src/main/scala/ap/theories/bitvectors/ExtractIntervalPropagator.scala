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

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    if (goal.facts.predConj.predicates.contains(_bv_extract)) {
      fwdPropagation(goal) ++ bwdPropagation(goal)
    } else {
      List()
    }

  /**
   * Propagate information about extract arguments to the extract result.
   */
  def fwdPropagation(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order : TermOrder = goal.order

    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
    val reducer  = goal.reduceWithFacts
    val proofs   = Param.PROOF_CONSTRUCTION(goal.settings)
    import reducer.{lowerBound, upperBound}

    val actions  = new ArrayBuffer[Plugin.Action]

    // TODO: cache results of lowerBound/upperBound?
    for (ex@Atom(_, Seq(Constant(ub), Constant(lb), arg, res), _) <-
            extracts) {
      (lowerBound(arg, proofs), upperBound(arg, proofs)) match {
        case (Some((argLB, argLBAsses)), Some((argUB, argUBAsses)))
            if lb <= ub => {

          commonBitsLB(argLB, argUB) match {
            case Some(bitBoundary) if ub + 1 >= bitBoundary => {
              val resLB = evalExtract(ub, lb, argLB)
              val resUB = evalExtract(ub, lb, argUB)

              val resConstraints = List(res - resLB, resUB - res) >= 0
              val redConstraints = reducer(resConstraints)

              if (!redConstraints.isTrue) {
                val action =
                  if (proofs)
                    Plugin.AddAxiom(argLBAsses ++ argUBAsses ++ List(ex),
                                    resConstraints,
                                    ModuloArithmetic)
                  else
                    Plugin.AddAxiom(List(),
                                    redConstraints,
                                    ModuloArithmetic)
                actions += action
                //-BEGIN-ASSERTION-///////////////////////////////////////////
                if (debug) {
                  println(
                    s"Inferred new bounds [$resLB, $resUB] for term $res")
                  println("\t" + action)
                }
                //-END-ASSERTION-/////////////////////////////////////////////
              }
            }
            case _ =>
              // nothing can be said
          }
        }

        case _ =>
          // nothing can be said
      }
    }

    actions.toSeq
  }

  /**
   * Propagate information about extract results to the extract arguments.
   */
  def bwdPropagation(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order : TermOrder = goal.order

    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
    val reducer  = goal.reduceWithFacts
    val proofs   = Param.PROOF_CONSTRUCTION(goal.settings)
    import reducer.{lowerBound, upperBound}

    val actions  = new ArrayBuffer[Plugin.Action]

    // TODO: make sure that the order of actions is deterministic
    for ((arg, exes) <- extracts.groupBy(_(2))) {
      lowerBound(arg, proofs) match {
        case Some((argLB, argLBAssumptions)) => {
          // check whether we can derive a tighter lower bound based on the
          // bounds on extracts
          val allAssumptions = new ArrayBuffer[Formula]
          allAssumptions ++= argLBAssumptions

          exes.head match {
          case Atom(_, Seq(Constant(IdealInt(headU)), _, _, _), _) => {
            var lastL = headU + 1
            var newArgLB = argLB >> lastL

            for (ex@Atom(_, Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
                                _, res), _) <- exes.iterator;
                  if ub < lastL) {
              lowerBound(res, proofs) match {
                case Some((resLB, resLBAssumptions)) if resLB.signum > 0 => {
                  newArgLB = (newArgLB << (lastL - lb)) + resLB
                  allAssumptions ++= resLBAssumptions
                  allAssumptions += ex
                  lastL = lb
                }
                case _ =>
              }
            }

            newArgLB = newArgLB << lastL

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
          case _ =>
            // bit indexes are too large
          }
        }

        case None => // without an initial lower bound, nothing can be done
      }

      upperBound(arg, proofs) match {
        case Some((argUB, argUBAssumptions)) => {
          // check whether we can derive a tighter upper bound based on the
          // bounds on extracts
          val allAssumptions = new ArrayBuffer[Formula]
          allAssumptions ++= argUBAssumptions

          exes.head match {
          case Atom(_, Seq(Constant(IdealInt(headU)), _, _, _), _) => {
            var lastL = headU + 1
            var newArgUB = argUB >> lastL

            for (ex@Atom(_, Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
                                _, res), _) <- exes.iterator;
                  if ub < lastL) {
              // add the 1-bits between the last and the current block
              newArgUB = newArgUB.shiftLeftAddOnes(lastL - ub - 1)

              upperBound(res, proofs) match {
                case Some((resUB, resUBAssumptions))
                    if resUB < pow2MinusOne(ub - lb + 1) => {
                  // add the upper bound on the current block
                  newArgUB = (newArgUB << (ub - lb + 1)) + resUB
                  allAssumptions ++= resUBAssumptions
                  allAssumptions += ex
                }
                case _ => {
                  // use the worst-case upper bound
                  newArgUB = newArgUB.shiftLeftAddOnes(ub - lb + 1)
                }
              }

              lastL = lb
            }

            // add remaining 1-bits after the last block
            newArgUB = newArgUB.shiftLeftAddOnes(lastL)

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
          case _ =>
            // bit indexes are too large
          }
        }

        case None => // without an initial lower bound, nothing can be done
      }
    }

    actions.toSeq
  }

}
