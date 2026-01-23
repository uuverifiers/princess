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

import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Formula, Term, ConstantTerm, TermOrder}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import LinearCombination.SingleTerm
import ap.terfor.conjunctions.Conjunction
import ap.theories.GroebnerMultiplication
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 HashSet => MHashSet}

object ModPlugin extends Plugin {

  import ModuloArithmetic._

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val predConj = goal.facts.predConj

      if (Seqs.disjoint(predConj.predicates,
                        Set(_bv_extract, _mod_cast,
                            _l_shift_cast, _r_shift_cast,
                            _bv_and, _bv_xor)))
        return List()

      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
      if (debug)
        printBVgoal(goal)
      //-END-ASSERTION-////////////////////////////////////////////////////////

      val actions =
      goalState(goal) match {
        case Plugin.GoalState.Eager =>
          negPreds(goal)                                  elseDo
          elimAtoms(goal)                                 elseDo
          ExtractPartitioner.handleGoal(goal)
        case Plugin.GoalState.Intermediate =>
          InEqSimplifier.handleGoal(goal)                 elseDo
          modShiftCast(goal)                              elseDo
          (ExtractIntervalPropagator.handleGoal(goal) ++
           BitwiseOpIntervalPropagator.handleGoal(goal))
        case Plugin.GoalState.Final =>
          modShiftCast(goal)                              elseDo
          ExtractArithEncoder.handleGoal(goal)
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (actions.isEmpty && debug)
        println("No bit-vector rules to apply!")
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions
    }

  /**
   * Generate an assertion that will cause all values of the given
   * term to be enumerated explicitly.
   */
  def enumIntValuesOf(t : Term, order : TermOrder) : Formula =
    GroebnerMultiplication.valueEnumerator.enumIntValuesOf(t, order)

  object NEEDS_SPLITTING extends Exception

  private def modShiftCast(goal : Goal) : Seq[Plugin.Action] = {
    // check if we have modcast or shiftcast actions
 /*   val actions1 =
      try {
        ModCastSplitter.modCastActions(goal, true)
      } catch {
        case NEEDS_SPLITTING =>
          // delayed splitting through a separate task
          List(Plugin.ScheduleTask(ModCastSplitter, 30))
      } */

    val actions2 =
      try {
        LShiftCastSplitter.shiftCastActions(goal, true)
      } catch {
        case NEEDS_SPLITTING =>
          // delayed splitting through a separate task
          List(Plugin.ScheduleTask(LShiftCastSplitter, 20))
      }

    val actions3 =
      try {
        RShiftCastSplitter.shiftCastActions(goal, true)
      } catch {
        case NEEDS_SPLITTING =>
          // delayed splitting through a separate task
          List(Plugin.ScheduleTask(RShiftCastSplitter, 20))
      }


    val res = /* actions1 ++ */ actions2 ++ actions3

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Mod Shift Casting:")
      for (a <- res)
        println("\t" + a)
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    res
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Replace negated predicates with positive predicates
   */
  private def negPreds(goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val actions1 =
      Plugin.makePredicatePositive(_mod_cast, goal, ModuloArithmetic) ++
      Plugin.makePredicatePositive(_l_shift_cast, goal, ModuloArithmetic)

    val negPreds2 =
      for (a <- goal.facts.predConj.negativeLitsWithPred(_bv_extract);
           // negative predicates can be handled only if bit arguments
           // are concrete (would need exponentiation function otherwise)
           if a(0).isConstant && a(1).isConstant)
      yield a

    val actions2 =
      if (!negPreds2.isEmpty) {
        (for (a <- negPreds2) yield {
          val sort@ModSort(sortLB, sortUB) =
            (SortedPredicate argumentSorts a).last
          val axiom =
            exists(Atom(a.pred, a.init ++ List(l(v(0))), order) &
              (v(0) >= sortLB) & (v(0) <= sortUB) & (v(0) =/= a.last))
          Plugin.AddAxiom(List(!conj(a)), axiom, ModuloArithmetic)
        }) ++ List(Plugin.RemoveFacts(conj(
                            for (a <- negPreds2) yield !conj(a))))
      } else {
        List()
      }

    val res = actions1 ++ actions2

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Negative predicate actions:")
      for (a <- res)
        println("\t" + a)
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimAtoms(goal : Goal) : Seq[Plugin.Action] = {
    // check whether there are atoms that we can eliminate
    val (castAtoms, (extractConsts, extractAtoms, extractDefs)) =
      eliminatableAtoms(goal)

    val castActions =
      if (!castAtoms.isEmpty) {
        val elimConsts =
          (for (a <- castAtoms; c <- a.last.constants) yield c).toSet
        val elimInEqs =
          InEqConj(
            for (lc <- goal.facts.arithConj.inEqs.iterator;
              if !Seqs.disjoint(elimConsts, lc.constants))
            yield lc,
            goal.order)
        val elimFormulas =
          Conjunction.conj(castAtoms ++ List(elimInEqs), goal.order)

        List(Plugin.RemoveFacts(elimFormulas),
          Plugin.AddReducableModelElement(elimFormulas, elimConsts,
            goal.reducerSettings))
      } else {
        List()
      }

    val extractActions =
      if (!extractConsts.isEmpty) {
        val elimInEqs =
          InEqConj(
            for (lc <- goal.facts.arithConj.inEqs.iterator;
              if !Seqs.disjoint(extractConsts, lc.constants))
            yield lc,
            goal.order)
        val elimFormulas =
          Conjunction.conj(extractAtoms ++ List(elimInEqs), goal.order)
        val allExtractDefs =
          Conjunction.conj(List(extractDefs, elimInEqs), goal.order)

        List(Plugin.RemoveFacts(elimFormulas),
          Plugin.AddReducableModelElement(allExtractDefs, extractConsts,
            goal.reducerSettings))
      } else {
        List()
      }

    val res = castActions ++ extractActions

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Eliminatable atoms actions:")
      for (a <- res)
        println("\t" + a)
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    res
  }

  /**
   * Find positive atoms in the goal that can be eliminated.
   */
  private def eliminatableAtoms(goal : Goal)
                  : (Seq[Atom],                     // cast lits
                     (Set[ConstantTerm], Seq[Atom], // extract lits
                      Conjunction)) = {
    val eliminatedIsolatedConstants = goal.eliminatedIsolatedConstants

    if (eliminatedIsolatedConstants.isEmpty)
      return (List(), (Set(), List(), Conjunction.TRUE))

    val facts = goal.facts

    val predConj = facts.predConj
    val castLits = predConj.positiveLitsWithPred(_mod_cast) ++
                   predConj.positiveLitsWithPred(_l_shift_cast)
    val extractLits = predConj.positiveLitsWithPred(_bv_extract)

    if (castLits.isEmpty && extractLits.isEmpty)
      return (List(), (Set(), List(), Conjunction.TRUE))

    val inEqs = facts.arithConj.inEqs

    // find constants that can be eliminated

    val constOccurs, unelimConsts = new MHashSet[ConstantTerm]
    unelimConsts ++= facts.arithConj.positiveEqs.constants
    unelimConsts ++= facts.arithConj.negativeEqs.constants
    unelimConsts ++= (for (a <- predConj.negativeLits.iterator;
                           c <- a.constants.iterator) yield c)
    unelimConsts ++= (for (lc <- inEqs.iterator;
                           if lc.constants.size >= 2;
                           c <- lc.constants.iterator) yield c)

    val lastLB = new MHashMap[ConstantTerm, Int]
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    val lastUB = new MHashMap[ConstantTerm, Int]
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    for (a <- predConj.positiveLits) a match {
      case Atom(`_bv_extract`,
                Seq(LinearCombination.Constant(IdealInt(ub)),
                    LinearCombination.Constant(IdealInt(lb)),
                    SingleTerm(c : ConstantTerm),
                    res),
                _)
          if !(unelimConsts contains c) &&
             ((lastLB get c) match {
               case Some(oldLB) =>
                 oldLB > ub
               case None =>
                 // if we haven't seen this constant in
                 // an extract literal yet, we must not have
                 // seen it at all
                 !(constOccurs contains c) &&
                 hasImpliedIneqConstraints(c, IdealInt.ZERO,
                                           pow2MinusOne(ub + 1), inEqs)
             }) => {
        constOccurs add c
        lastLB.put(c, lb)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        // we rely on the fact that the extract literals are sorted
        // in decreasing order
        Debug.assertInt(AC, ub <= lastUB.getOrElse(c, Int.MaxValue))
        lastUB.put(c, ub)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        unelimConsts ++= res.constants
      }
      case Atom(`_bv_extract`, _, _) =>
        for (lc <- a.iterator; c <- lc.constants.iterator)
          unelimConsts add c
      case a =>
        for (lc <- a.iterator; c <- lc.constants.iterator)
          if (!(constOccurs add c))
            unelimConsts add c
    }

    // find cast atoms with those constants

    val castElims =
      for (a@Atom(_,
                  Seq(LinearCombination.Constant(lower),
                      LinearCombination.Constant(upper),
                      _*),
                  _) <- castLits;
           SingleTerm(resConst : ConstantTerm) <- List(a.last);
           if (eliminatedIsolatedConstants contains resConst) &&
               !(unelimConsts contains resConst) &&
               hasImpliedIneqConstraints(resConst, lower, upper, inEqs))
      yield a

    // find extract atoms with those constants

    val backTranslation =
      new MHashMap[ConstantTerm, ArrayBuffer[(IdealInt, LinearCombination)]]

    val extractElims =
      for (a@Atom(_,
                  Seq(_,
                      LinearCombination.Constant(lb),
                      SingleTerm(c : ConstantTerm),
                      res),
                  _) <- extractLits;
           if (eliminatedIsolatedConstants contains c) &&
               !(unelimConsts contains c)) yield {
        backTranslation.getOrElseUpdate(c, new ArrayBuffer) += ((pow2(lb), res))
        a
      }

    implicit val order = goal.order
    import TerForConvenience._

    val extractDefs : Conjunction =
      eqZ(for ((c, parts) <- backTranslation) yield {
            parts += ((IdealInt.MINUS_ONE, LinearCombination(c, order)))
            LinearCombination.sum(parts, order)
          })

    (castElims, (backTranslation.keySet.toSet, extractElims, extractDefs))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether all inequalities present for the given constants are
   * already implied by the type
   */
  protected[bitvectors] def hasImpliedIneqConstraints(
                              c : ConstantTerm,
                              lower : IdealInt,
                              upper : IdealInt,
                              ineqs : InEqConj) : Boolean =
      ineqs forall { lc =>
        !(lc.constants contains c) ||
        (lc.constants.size == 1 &&
         (lc.leadingCoeff match {
            case IdealInt.ONE       => -lc.constant <= lower
            case IdealInt.MINUS_ONE => lc.constant >= upper
            case _                  => false
          }))
      }

  //////////////////////////////////////////////////////////////////////////////

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def printBVgoal(goal : Goal) = {
    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
    val diseqs = goal.facts.arithConj.negativeEqs
    val ineqs = goal.facts.arithConj.inEqs

    println()
    println("Calling theory solver: ModuloArithmetic")

    if (!goal.facts.predConj.positiveLits.filterNot(_.pred.name == "bv_extract").isEmpty) {
      println("+--------------------------PREDCONJ----------------------+")
      for (f <- goal.facts.predConj.positiveLits.filterNot(_.pred.name == "bv_extract"))
        println("|\t" + f)
    }

    if (!extracts.isEmpty) {
      println("+--------------------BVEXTRACTS--------------------------+")
      for (ex <- extracts) {
        println("|\t" + ex)
      }
    }
    if (!diseqs.isEmpty) {
      println("+----------------------DISEQS---------------------------+")
      for (diseq <- diseqs) {
        println("|\t" + diseq + " != 0")
      }
    }
     if (!ineqs.isTrue) {
      println("+----------------------INEQS---------------------------+")
      for (ie <- goal.facts.arithConj.inEqs) {
        println("|\t" + ie + " >= 0")
      }
    }
    println("+-------------------------------------------------------+")
  }
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
}
