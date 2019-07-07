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

import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula, Term, ConstantTerm, OneTerm}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import LinearCombination.SingleTerm
import ap.types.SortedPredicate
import ap.util.Debug

import scala.collection.mutable.{LinkedHashMap, HashSet => MHashSet}

/**
 * ExtractArithEncoder translates bv_extract to an existentially quantified
 * equation
 */
object ExtractArithEncoder extends TheoryProcedure {

  import ModuloArithmetic._
  import ModPlugin.hasImpliedIneqConstraints

  private val AC = Debug.AC_MODULO_ARITHMETIC

    def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      encode(goal, false)

    def encode(goal : Goal, encodeAll : Boolean) : Seq[Plugin.Action] =  {
      import TerForConvenience._
      implicit val order = goal.order

      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
      val inEqs = goal.facts.arithConj.inEqs

      if (extracts.isEmpty)
        return List()

      val terms =
        new LinkedHashMap[LinearCombination,
                          (Int, Int, List[(IdealInt, Term)],
                           Int, List[LinearCombination],
                           List[Atom])]
      val ignoredTerms =
        new MHashSet[LinearCombination]

      def elimExtract(ex : Atom,
                      ub : Int, lb : Int,
                      arg : LinearCombination,
                      res : LinearCombination) : Unit = {
        (terms get arg) match {
          case None =>
            terms.put(arg, (ub, lb, List((pow2(lb), res)), 0, List(), List(ex)))
          case Some((firstUB, lastLB, ts, nextVarInd, constraints, atoms)) =>
            if (lastLB > ub + 1) {
              // need to put a quantified variable in between
              val vv = v(nextVarInd)
              val newTS = (pow2(lb), res) :: (pow2(ub + 1), vv) :: ts
              val newConstraints =
                LinearCombination(List((IdealInt.MINUS_ONE, l(vv)),
                                      (pow2MinusOne(lastLB - ub - 1), OneTerm)),
                                  order) ::
                (l(vv)) :: constraints
              terms.put(arg, (firstUB, lb, newTS,
                              nextVarInd+1, newConstraints, ex :: atoms))
            } else if (lastLB == ub + 1) {
              // no variable needed
              terms.put(arg, (firstUB, lb, (pow2(lb), res) :: ts,
                              nextVarInd, constraints, ex :: atoms))
            } else if (SingleTerm.unapply(arg).isDefined) {
              // This extract cannot be eliminated, since it
              // overlaps with the last one. In this case we don't
              // eliminate extracts for this term altogether at this
              // point, we wait until the extracts have been split
              terms -= arg
              ignoredTerms += arg
            } else {
              // Extract applied to a complex term, and the ranges overlap
              // with the previous extract. Such extracts will not be
              // fully split, so we just ignore this literal for the time
              // being, and translate the other ones to arithmetic.
            }
        }
      }

      val arithExtractedConsts = new MHashSet[ConstantTerm]

      if (encodeAll)
        arithExtractedConsts ++= goal.facts.constants
      else
        arithExtractedConsts ++= arithmeticExtractedConsts(goal)

      for (ex <- extracts) ex match {
        case Atom(`_bv_extract`,
                  Seq(_,
                      _,
                      arg,
                      _),
                  _) if (ignoredTerms contains arg) =>
          // nothing
        case Atom(`_bv_extract`,
                  Seq(LinearCombination.Constant(IdealInt(ub)),
                      LinearCombination.Constant(IdealInt(lb)),
                      arg@SingleTerm(c : ConstantTerm),
                      res),
                  _) =>
          if ((arithExtractedConsts contains c) ||
              !hasImpliedIneqConstraints(c, IdealInt.ZERO,
                                         pow2MinusOne(ub + 1), inEqs)) {
            arithExtractedConsts += c
            elimExtract(ex, ub, lb, arg, res)
          }
        case Atom(`_bv_extract`,
                  Seq(LinearCombination.Constant(IdealInt(ub)),
                      LinearCombination.Constant(IdealInt(lb)),
                      arg,
                      res),
                  _) =>
          elimExtract(ex, ub, lb, arg, res)
        case _ =>
          // nothing
      }

      if (terms.isEmpty)
        return List()

      // if necessary, add a variable for the least-significant bits
      for (arg <- terms.keys) terms(arg) match {
        case (_, 0, _, _, _, _) =>
          // nothing
        case (_, lastUB, _, _, _, atoms) =>
          elimExtract(atoms.head, -1, 0, arg, l(0))
      }

      val axioms =
        for ((arg, (firstUB, lastLB, ts, varNum,
                    constraints, atoms)) <- terms) yield {
          val modRes = LinearCombination(ts, order)
          val defFor =
            exists(varNum,
                   conj(constraints >= 0,
                        _mod_cast(List(l(0), l(pow2MinusOne(firstUB+1)),
                                       l(arg), modRes))))
          Plugin.AddAxiom(atoms.distinct, defFor, ModuloArithmetic)
        }

      val toRemove =
        conj(for (Plugin.AddAxiom(atoms, _, _) <- axioms.iterator;
                  a <- atoms.iterator)
             yield a)

      val actions = List(Plugin.RemoveFacts(toRemove)) ++ axioms

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug) {
        println("Extract to arithmetic:")
        for (a <- actions)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions
    }

    /**
     * Determine constants that occur in general arithmetic context.
     */
    private def arithmeticExtractedConsts(goal : Goal)
                                        : MHashSet[ConstantTerm] = {
      val arithConsts = new MHashSet[ConstantTerm]

      val facts = goal.facts
      val ac = facts.arithConj

      arithConsts ++= ac.positiveEqs.constants

      for (lc <- ac.inEqs)
        if (lc.constants.size > 1)
          arithConsts ++= lc.constants

      for (a <- facts.predConj.positiveLits) a match {
        case Atom(`_bv_extract`,
                  Seq(_, _, SingleTerm(_), _), _) =>
          // nothing
        case Atom(`_bv_extract`,
                  Seq(_,  _, arg, _), _) =>
          arithConsts ++= arg.constants
        case a =>
          arithConsts ++= a.constants
      }

      for (a <- facts.predConj.negativeLits)
        arithConsts ++= a.constants

      arithConsts
    }
  }
