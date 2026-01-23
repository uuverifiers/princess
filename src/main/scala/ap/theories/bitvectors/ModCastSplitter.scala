/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2025 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.{TerForConvenience, Formula, TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

import scala.collection.mutable.ArrayBuffer

/**
 * Splitter handles the splitting of mod_cast-operations, when no other
 * inference steps are possible anymore.
 */
object ModCastSplitter
       extends TermBasedSaturationProcedure(
          "ModCastSplitter",
          arity           = 4,
          basePriority    = ModuloArithmetic.MOD_CAST_SPLITTER_PRIORITY,
          priorityUpdates = true) {

  import ModuloArithmetic._

  private val SPLIT_LIMIT = IdealInt(20)

  private
    def analyseBounds(goal : Goal, a : Atom, proofs : Boolean)
                          : Option[(IdealInt,             // lowerBound
                                    IdealInt,             // lowerFactor
                                    IdealInt,             // upperBound
                                    IdealInt,             // upperFactor
                                    Seq[Formula])] = {    // assumptions
    val propagator = goal.reduceWithFacts
    var assumptions : List[Formula] = List(a)

    def addInEqAssumption(ineqs : Seq[Formula]) =
      for (f <- ineqs)
        assumptions = f :: assumptions

    val lBound =
      if (proofs)
        for ((b, assum) <- propagator.lowerBound(a(2), true)) yield {
          addInEqAssumption(assum)
          b
        }
      else
        propagator lowerBound a(2)

    val uBound =
      if (lBound.isDefined) {
        if (proofs)
          for ((b, assum) <- propagator.upperBound(a(2), true)) yield {
            addInEqAssumption(assum)
            b
          }
        else
          propagator upperBound a(2)
      } else {
        None
      }

    for (lb <- lBound; ub <- uBound) yield {
      val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last
      val lowerFactor = (lb - sortLB) / sort.modulus
      val upperFactor = -((sortUB - ub) / sort.modulus)
      (lb, lowerFactor, ub, upperFactor, assumptions)
    }
  }

  def extractApplicationPoints(goal : Goal) : Iterator[ApplicationPoint] = {
    val predConj = goal.facts.predConj
    predConj.positiveLitsWithPred(_mod_cast).iterator.map(_.toVector)
  }

  def applicationPriority(goal : Goal, args : ApplicationPoint) : Int = {
    val order = goal.order
    val a = Atom(_mod_cast, args, order)
    analyseBounds(goal, a, false) match {
      case Some((_, lowerFactor, _, upperFactor, _)) => {
        val caseNum = upperFactor - lowerFactor + 1
        (caseNum min SPLIT_LIMIT).intValueSafe * 10
      }
      case None =>
        SPLIT_LIMIT.intValueSafe * 10
    }
  }

  def handleApplicationPoint(goal : Goal,
                             args : ApplicationPoint) : Seq[Plugin.Action] = {
    implicit val order : TermOrder = goal.order
    import TerForConvenience._

    val a = Atom(_mod_cast, args, order)

    if (goal.facts.predConj.positiveLitsAsSet.contains(a)) {
      val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last
      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      val actions = new ArrayBuffer[Plugin.Action]
      actions += Plugin.RemoveFacts(a)

      analyseBounds(goal, a, proofs) match {
        case Some((lb, lowerFactor, ub, upperFactor, assumptions))
            if upperFactor - lowerFactor + 1 <= SPLIT_LIMIT => {
          val wastedLower = lb - (lowerFactor * sort.modulus + sortLB)
          val wastedUpper = (upperFactor * sort.modulus + sortUB) - ub

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // mod_casts with only one case should have been handled by the
          // reducer already!
          Debug.assertInt(AC, lowerFactor < upperFactor)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          val cases =
            (for (n <-
                    // consider the inner cases first
                    IdealRange(lowerFactor + 1, upperFactor).iterator ++
                    (if (wastedLower < wastedUpper)
                       Seqs.doubleIterator(lowerFactor, upperFactor)
                     else
                       Seqs.doubleIterator(upperFactor, lowerFactor));
                  f = conj(a(2) === a(3) + (n * sort.modulus));
                  if !f.isFalse)
             yield (f, List())).toBuffer

          actions += Plugin.AxiomSplit(assumptions.distinct,
                                       cases.toList,
                                       ModuloArithmetic)
        }
        case _ => {
          actions +=
            Plugin.AddAxiom(List(a),
                            exists(a(2) === a(3) + (v(0) * sort.modulus)),
                            ModuloArithmetic)
        }
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug && !actions.isEmpty) {
        println("Mod Casting:")
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
