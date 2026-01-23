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
object ModCastSplitter2
       extends TermBasedSaturationProcedure("ModCastSplitter",
                                            arity           = 4,
                                            basePriority    = 10,
                                            priorityUpdates = true) {

  import ModuloArithmetic._
  import ModCastSplitter.{analyseBounds, SPLIT_LIMIT}

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

/**
 * Splitter handles the splitting of mod_cast-operations, when no other
 * inference steps are possible anymore.
 */
object ModCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  // TODO: backward propagation for the mod_cast function

  protected[bitvectors] val SPLIT_LIMIT = IdealInt(20)

  protected[bitvectors]
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

  protected[bitvectors] def modCastActions(goal : Goal, noSplits : Boolean)
                                          : Seq[Plugin.Action]={
    val castPreds =
      goal.facts.predConj.positiveLitsWithPred(_mod_cast).toBuffer
    // TODO: handle occurring _mul predicates in a special way?

    Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

    val propagator = goal.reduceWithFacts
    implicit val order : TermOrder = goal.order
    import TerForConvenience._

    // find simple mod_cast predicates that can be replaced by equations
    var simpleElims : List[Plugin.Action] = List()

    // find a mod_cast predicate that can be split into a small number of
    // cases
    var bestSplitNum = SPLIT_LIMIT
    var bestSplitPred : Option[(Atom,
                                IdealInt, // lowerFactor
                                IdealInt, // upperFactor
                                IdealInt, // wastedLower
                                IdealInt, // wastedUpper
                                Seq[Formula], ModSort)] = None

    // find a predicate that has to be eliminated through a quantifier
    var someQuantPred : Option[Atom] = None

    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

    for (a <- castPreds) {
      analyseBounds(goal, a, proofs) match {
        case Some((lb, lowerFactor, ub, upperFactor, assumptions)) => {
          val sort@ModSort(sortLB, sortUB) = (SortedPredicate argumentSorts a).last

          if (lowerFactor == upperFactor) {
            // in this case, no splitting is necessary

            simpleElims =
              Plugin.RemoveFacts(a) ::
              Plugin.AddAxiom(
                      assumptions.distinct,
                      a(2) === a(3) + (lowerFactor * sort.modulus),
                      ModuloArithmetic) :: simpleElims
                      
          } else if (simpleElims.isEmpty) {
          
            val caseNum = upperFactor - lowerFactor + 1

            if (someQuantPred.isEmpty && caseNum >= SPLIT_LIMIT) {
              someQuantPred =
                Some(a)
            } else if (caseNum < bestSplitNum) {
              bestSplitNum =
                caseNum
              val wastedLower =
                lb - (lowerFactor * sort.modulus + sortLB)
              val wastedUpper =
                (upperFactor * sort.modulus + sortUB) - ub
              bestSplitPred =
                Some((a, lowerFactor, upperFactor,
                      wastedLower, wastedUpper, assumptions, sort))
            }
          }
        }
        case None => {
          someQuantPred = Some(a)
        }
      }
    }

    val res =
    if (!simpleElims.isEmpty) {

      simpleElims

    } else if (bestSplitPred.isDefined) {

      if (noSplits)
        throw ModPlugin.NEEDS_SPLITTING

      val Some((a, lowerFactor, upperFactor,
                wastedLower, wastedUpper, assumptions, sort)) =
        bestSplitPred

      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
      Debug.assertInt(AC, lowerFactor < upperFactor)
      //-END-ASSERTION-///////////////////////////////////////////////////////

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

      List(Plugin.RemoveFacts(a),
            Plugin.AxiomSplit(assumptions.distinct,
                              cases.toList,
                              ModuloArithmetic))
      
    } else if (someQuantPred.isDefined) {

      val Some(a) =
        someQuantPred
      val sort =
        (SortedPredicate argumentSorts a).last.asInstanceOf[ModSort]

      List(Plugin.RemoveFacts(a),
            Plugin.AddAxiom(List(a),
                            exists(a(2) === a(3) + (v(0) * sort.modulus)),
                            ModuloArithmetic))

    } else {

      List()

    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println("\t" + res)
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println()
      println("mod_cast splitter ...")
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    modCastActions(goal, false)
  }
}
