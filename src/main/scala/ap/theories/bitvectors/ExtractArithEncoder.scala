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

import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula, Term, ConstantTerm, OneTerm,
                  TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import LinearCombination.{SingleTerm, Constant}
import ap.types.SortedPredicate
import ap.util.Debug

import scala.collection.mutable.{LinkedHashMap, HashSet => MHashSet,
                                 HashMap => MHashMap}

/**
 * ExtractArithEncoder translates bv_extract to an existentially quantified
 * equation
 */
object ExtractArithEncoder extends TheoryProcedure {

  import ModuloArithmetic._
  import ModPlugin.hasImpliedIneqConstraints

    def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      encode(goal, false)

    def encode(goal : Goal, encodeAll : Boolean) : Seq[Plugin.Action] =  {
      import TerForConvenience._
      implicit val order : TermOrder = goal.order

      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
      if (extracts.isEmpty)
        return List()

      val inEqs = goal.facts.arithConj.inEqs

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
                  Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
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
                  Seq(Constant(IdealInt(ub)), Constant(IdealInt(lb)),
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
      val reduceWithFacts = goal.reduceWithFacts

      arithConsts ++= ac.positiveEqs.constants

      for (lc <- ac.inEqs)
        if (lc.constants.size > 1)
          arithConsts ++= lc.constants

      for (a <- facts.predConj.negativeLits)
        arithConsts ++= a.constants

      // find constants whose value is completely determined by
      // extracts, as well as extracts on more complex terms

      val lastLB = new MHashMap[ConstantTerm, IdealInt]
      val blockedConsts = new MHashSet[ConstantTerm]

      for (a <- facts.predConj.positiveLits) a match {
        case Atom(`_bv_extract`,
                  Seq(Constant(IdealInt(upper)), Constant(IdealInt(lower)),
                      SingleTerm(c : ConstantTerm), Constant(_)),
                  _) =>
          if (!(arithConsts contains c) &&
              !(blockedConsts contains c)) (lastLB get c) match {
            case Some(lb) =>
              if (upper + IdealInt.ONE == lb)
                lastLB.put(c, lower)
              else
                blockedConsts += c
            case None => {
              for (ub <- reduceWithFacts.upperBound(c);
                   if ub <= pow2MinusOne(upper+1);
                   lb <- reduceWithFacts.lowerBound(c);
                   if lb.signum >= 0)
                lastLB.put(c, lower)
              if (!(lastLB contains c))
                blockedConsts += c
            }
          }
        case Atom(`_bv_extract`,
                  Seq(_, _, SingleTerm(c : ConstantTerm), _),
                  _) =>
          blockedConsts += c
        case Atom(`_bv_extract`,
                  Seq(_,  _, arg, _), _) =>
          arithConsts ++= arg.constants
        case a =>
          arithConsts ++= a.constants
      }

      for ((c, IdealInt.ZERO) <- lastLB)
        if (!(blockedConsts contains c))
          arithConsts += c

      arithConsts
    }
  }
