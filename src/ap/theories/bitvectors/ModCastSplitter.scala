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
import ap.terfor.{TerForConvenience, Formula}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

/**
 * Splitter handles the splitting of mod_cast-operations, when no other
 * inference steps are possible anymore.
 */
object ModCastSplitter extends TheoryProcedure {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  // TODO: backward propagation for the mod_cast function

  private val SPLIT_LIMIT = IdealInt(20)

    protected[bitvectors] def modCastActions(goal : Goal, noSplits : Boolean)
                                           : Seq[Plugin.Action]={
      val castPreds =
        goal.facts.predConj.positiveLitsWithPred(_mod_cast).toBuffer
      // TODO: handle occurring _mul predicates in a special way?

      Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

      val propagator = IntervalPropagator(goal)
      implicit val order = goal.order
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
                                  List[Formula], ModSort)] = None

      // find a predicate that has to be eliminated through a quantifier
      var someQuantPred : Option[Atom] = None

      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      for (a <- castPreds) {
        var assumptions : List[Formula] = List(a)

        def addInEqAssumption(ineqs : Seq[Formula]) =
          for (f <- ineqs)
            assumptions = f :: assumptions

        val lBound =
          if (proofs)
            for ((b, assum) <-
                   propagator lowerBoundWithAssumptions a(2)) yield {
              addInEqAssumption(assum)
              b
            }
          else
            propagator lowerBound a(2)

        val uBound =
          if (lBound.isDefined) {
            if (proofs)
              for ((b, assum) <-
                     propagator upperBoundWithAssumptions a(2)) yield {
                addInEqAssumption(assum)
                b
              }
            else
              propagator upperBound a(2)
          } else {
            None
          }

        (lBound, uBound) match {
          case (Some(lb), Some(ub)) => {
            val sort@ModSort(sortLB, sortUB) =
              (SortedPredicate argumentSorts a).last

            val lowerFactor = (lb - sortLB) / sort.modulus
            val upperFactor = -((sortUB - ub) / sort.modulus)

            if (lowerFactor == upperFactor) {
              // in this case, no splitting is necessary

              simpleElims =
                Plugin.RemoveFacts(a) ::
                Plugin.AddAxiom(
                       assumptions,
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

          case _ =>
            someQuantPred = Some(a)
        }
      }

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
             Plugin.AxiomSplit(assumptions,
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
    }

  def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    if (debug) {
      println
      println("mod_cast splitter ...")
    }
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    modCastActions(goal, false)
  }
}
