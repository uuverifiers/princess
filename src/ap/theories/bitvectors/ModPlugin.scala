/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2022 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.{TerForConvenience, Formula, Term, ConstantTerm, TermOrder,
                  VariableTerm}
import ap.terfor.preds.Atom
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import LinearCombination.SingleTerm
import ap.terfor.conjunctions.Conjunction
import ap.types.SortedPredicate
import ap.util.{Debug, Seqs, IdealRange}

import scala.collection.mutable.{ArrayBuffer, Map => MMap, HashMap => MHashMap,
                                 HashSet => MHashSet}

object ModPlugin extends Plugin {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      val predConj = goal.facts.predConj

      if (Seqs.disjoint(predConj.predicates,
                        Set(_bv_extract, _mod_cast,
                            _l_shift_cast, _r_shift_cast)))
        return List()

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug)
        printBVgoal(goal)
     //-END-ASSERTION-//////////////////////////////////////////////////////////

      val negPs = negPreds(goal)
      if (!negPs.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Negative predicate actions:")
          for (a <- negPs)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return negPs
      }

      val elimActions = elimAtoms(goal)
      if (!elimActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Eliminatable atoms actions:")
          for (a <- elimActions)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return elimActions
      }

      // extract-predicates in the goal

      val extracts = predConj.positiveLitsWithPred(_bv_extract) //  getExtracts(goal)

      if (!extracts.isEmpty) {
        // If necessary, turn extracts in arithmetic context into
        // just arithmetic constaints

        val actions = ExtractArithEncoder.handleGoal(goal)
        if (!actions.isEmpty)
          return actions

//        actions += Plugin.ScheduleTask(ExtractArithEncoder, 10)
      }

      val extractedConsts =
        (for (Seq(_, _, SingleTerm(c : ConstantTerm), _) <- extracts.iterator)
         yield c).toSet

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      for (ex <- extracts) {
        Debug.assertInt(AC,
          ex(0).asInstanceOf[LinearCombination0].constant.signum >= 0 &&
          ex(1).asInstanceOf[LinearCombination0].constant.signum >= 0)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val diseqs = for (lc <- goal.facts.arithConj.negativeEqs;
                        if !Seqs.disjoint(lc.constants, extractedConsts))
                   yield lc
      val partitions = computeCutPoints(extracts, diseqs)

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug && !partitions.isEmpty) {
        println("<<Partitions>>")
        for ((k, v) <- partitions){
          println("\t" + k + " --> " + v)
        }
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      // Let's start by only splitting one variable
      val splitActions = splitExtractActions(extracts, partitions, goal)

      if (!splitActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Splitting extracts")
          for (t <- splitActions)
            println("\t" + t)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return splitActions
      }

      val diseqActions = splitDisequalityActions(diseqs, partitions, goal) /* ++
                         splitDisInequalityActions(pureExtractedConsts,
                                                   partitions,
                                                   goal) ++
                         splitDisInequalityActions2(pureExtractedConsts,
                                                    partitions,
                                                    goal) */
      if (!diseqActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Splitting disequalities actions:")
          for (t <- diseqActions)
            println("\t" + t)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return diseqActions
      }

      val msc = modShiftCast(goal)
      if (!msc.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Mod Shift Casting:")
          for (a <- msc)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return msc
      }

      if ((goalState(goal) == Plugin.GoalState.Final) && (!extracts.isEmpty)) {
        // if there is nothing else we can do, replace all extracts with
        // arithmetic constraints
        val actions = ExtractArithEncoder.encode(goal, true)
        if (!actions.isEmpty)
          return actions
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug)
        println("Nothing..")
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      List()
    }

  object NEEDS_SPLITTING extends Exception

  private def modShiftCast(goal : Goal) : Seq[Plugin.Action] = {
    // check if we have modcast or shiftcast actions
    val actions1 =
      try {
        ModCastSplitter.modCastActions(goal, true)
      } catch {
        case NEEDS_SPLITTING =>
          // delayed splitting through a separate task
          List(Plugin.ScheduleTask(ModCastSplitter, 30))
      }

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

    actions1 ++ actions2 ++ actions3
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  //   |EXTRACT| PROPAGATION
  //
  // Extract uses SMT-lib semantics
  // If we have extract(7,3)....
  // What are cut-points.
  // They should represent points in between which we have intervas
  // We should let the first arugment be exclusive
  // e.g., extract(7,3) is cut-point 8 and 3
  // Thus, when looping we get (7,3) and (2,0) in SMT-lib semantics

  private def getExtracts(goal : Goal) : Seq[Atom] = {
    // first check if congruence closure has been fully applied

    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)

    var lastAtom : Atom = null
    val atomIt = extracts.iterator
    while (atomIt.hasNext) {
      val a = atomIt.next
      
      if (a(2).isConstant)
        // extract can be evaluated, delay all operations on extracts
        return List()
        
      if (lastAtom != null &&
          lastAtom(0) == a(0) && lastAtom(1) == a(1) && lastAtom(2) == a(2))
        // a case where functionality axiom can be applied;
        // in this case, delay all operations of the extracts
        return List()
        
      lastAtom = a
    }

    extracts
  }

  // This propagates all cut-points from lhs <-> rhs in extract

  private def propagateExtract(extract : (Int, Int, ConstantTerm, ConstantTerm),
                               cutPoints : MMap[Term, Set[Int]]) : Boolean = {
    val (ub, lb, t1, t2) = extract

    var changed = false

    val cut1 = cutPoints.getOrElse(t1, Set())
    val cut2 = cutPoints.getOrElse(t2, Set())

    /// T1 ===> T2
    val t1transformed =
      cut1.map(_ - lb).filter(c => c > 0 && c <= ub - lb + 1)

    if (!(t1transformed subsetOf cut2)) {
      cutPoints += t2 -> (cut2 ++ t1transformed)
      changed = true
    }

    // propagate FROM t2 TO t1
    val t2transformed = cut2.map(_ + lb).filter(c => c <= ub)

    if (!(t2transformed subsetOf cut1)) {
      cutPoints += t1 -> (cut1 ++ t2transformed)
      changed = true
    }

    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertInt(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-/////////////////////////////////////////////////////////

    changed
  }

  private def propagateDisequality(disequality : (ConstantTerm, ConstantTerm),
                                   cutPoints : MMap[Term, Set[Int]])
                                 : Boolean = {
    val (t1, t2) = disequality
    var changed = false

    val t1cuts = cutPoints.getOrElse(t1, Set())
    val t2cuts = cutPoints.getOrElse(t2, Set())
        
    if (!(t1cuts subsetOf t2cuts)) {
      cutPoints += t2 -> (t2cuts ++ t1cuts)
      changed = true
    }

    if (!(t2cuts subsetOf t1cuts)) {
      cutPoints += t1 -> (t1cuts ++ t2cuts)
      changed = true
    }

    changed
  }

  private def computeCutPoints(extracts : Seq[Atom],
                               disequalities : Seq[LinearCombination])
                             : Map[Term, List[Int]] = {
    val cutPoints = MMap() : MMap[Term, Set[Int]]
    val extractTuples = new ArrayBuffer[(Int, Int, ConstantTerm, ConstantTerm)]
    val diseqTuples = new ArrayBuffer[(ConstantTerm, ConstantTerm)]

    for (Seq(LinearCombination.Constant(IdealInt(ub)),
             LinearCombination.Constant(IdealInt(lb)),
             SingleTerm(t : ConstantTerm),
             res) <- extracts) {
      cutPoints += t -> (Set(lb, ub+1) ++ (cutPoints.getOrElse(t, Set())))
      res match {
        case SingleTerm(s : ConstantTerm) =>
          extractTuples += ((ub, lb, t, s))
        case _ =>
          // nothing
      }
    }

    for (lc <- disequalities)
      if (lc.size == 2 &&
          lc.getCoeff(0) == IdealInt.ONE &&
          lc.getCoeff(1) == IdealInt.MINUS_ONE &&
          lc.constants.size == 2)
        diseqTuples += ((lc.getTerm(0).asInstanceOf[ConstantTerm],
                         lc.getTerm(1).asInstanceOf[ConstantTerm]))

    var changed = true
    while (changed) {
      changed = false
      for (t <- extractTuples) {
        if (propagateExtract(t, cutPoints))
          changed = true
      }

      for (diseq <- diseqTuples) {
        if (propagateDisequality(diseq, cutPoints))
          changed = true
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    cutPoints.map{case (k, v) => k -> v.toList.sorted.reverse}.toMap
  }


  ///////////////////////////
  //
  // EXTRACT (and Diseq) SPLIT FUNCTIONS
  //
  //
  //
  // PRE-CONDITION: parts must have been created using extract (i.e., we can't have
  // extract(1,3) and parts being (0,2) ^ (2,4), but parts should be (0,1) ^ (1,2) ^ (2,3) ^ (3,4)
  private def splitExtract(extract : Atom, cutPoints : List[Int])
                          (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    val Seq(LinearCombination.Constant(IdealInt(upper)),
            LinearCombination.Constant(IdealInt(lower)),
            t1, t2) = extract

    var filterCutPoints = cutPoints.filter(x => x >= lower && x <= upper)

    if (filterCutPoints.length < 2) {
      List()
    } else {
      var curPoint = upper
      var newExtracts = List() : List[Conjunction]

      while (!filterCutPoints.isEmpty) {
        val (ub, lb) = (curPoint, filterCutPoints.head)
        filterCutPoints = filterCutPoints.tail
        curPoint = lb - 1

        val bv1 =
          Atom(_bv_extract,
               List(l(ub),       l(lb),       l(t1), l(v(0))), order)
        val bv2 =
          Atom(_bv_extract,
               List(l(ub-lower), l(lb-lower), l(t2), l(v(0))), order)
        val domain = List(l(v(0)) >= 0, l(v(0)) < pow2(ub-lb+1))
        newExtracts = forall(!conj(bv1 :: bv2 :: domain)) :: newExtracts
      }
      Plugin.RemoveFacts(extract) ::
      (for (c <- newExtracts)
       yield Plugin.AddAxiom(List(extract), !c, ModuloArithmetic))
    }
  }

  private def splitDiseq(disequality : LinearCombination,
                         cutPoints : List[Int], goal : Goal)
                        (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    // Make sure c1 != c2 according to cutPoints
    def split(c1 : Term, c2 : Term) : List[Plugin.Action] = {
      val upperBounds : List[IdealInt] = (List(c1,c2).map{
        x => {
          val lc = LinearCombination(IdealInt.MINUS_ONE, x, order)
          goal.facts.arithConj.inEqs.findLowerBound(lc) match {
            case Some(b) => -b
            case None => IdealInt(0)
          }
        }})

      // TODO: Can equality between bit-vectors of diff size be equal?
      val upper = upperBounds.max

      if (upper.signum <= 0)
        return List()

      val bits = upper.getHighestSetBit + 1
      val remCutPoints = for (p <- cutPoints; if 0 < p && p < bits) yield p
      val allPoints = bits :: remCutPoints ::: List(0)

      // We store with upper bound non-exclusive
      var curPoint = allPoints.head - 1
      var iterPoints = allPoints.tail
      var newExtracts = List() : List[Formula]
      var variables = List() : List[(VariableTerm, Int)]

      if (iterPoints.length == 1)
        return List()

      while (!iterPoints.isEmpty) {
        val ub = curPoint
        val lb = iterPoints.head
        iterPoints = iterPoints.tail

        val bitLength = ub - lb + 1
        curPoint = lb - 1

        val (v1, v2) = (v(variables.length), v(variables.length+1))
        variables = (v2, bitLength) :: (v1, bitLength) :: variables
        val (tmp1, tmp2) = (l(v1), l(v2))

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, ub >= 0)
        Debug.assertInt(AC, lb >= 0)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val bv1 = Atom(_bv_extract, List(l(ub), l(lb), l(c1), tmp1), order)
        val bv2 = Atom(_bv_extract, List(l(ub), l(lb), l(c2), tmp2), order)

        val upper = pow2MinusOne(bitLength)
        newExtracts =
          (tmp1 >= 0) :: (tmp1 <= upper) ::
          (tmp2 >= 0) :: (tmp2 <= upper) :: bv1 :: bv2 :: newExtracts
      }

      val diseqs =
        (for (List((v1, bl1), (v2, bl2)) <- variables.sliding(2,2)) yield {
          // TODO: Remove this if domains are not relevant
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, bl1 == bl2)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          v1 === v2
          // conj(v1 >= 0, v1 < pow2(bl1), v2 >= 0, v2 < pow2(bl2), v1 === v2)
        })

      val subFormula = conj(newExtracts) & !conj(diseqs)
      val finalConj = exists(variables.length, subFormula)
      (Plugin.RemoveFacts(disequality =/= 0)) ::
       List(Plugin.AddAxiom(List(disequality =/= 0),
                            finalConj,
                            ModuloArithmetic))
    }

    if (cutPoints.isEmpty) {
      List()
    } else if (disequality.constants.size == 1) {
      // -Constant and Integer
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, disequality.leadingCoeff.isOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      split(disequality.leadingTerm, l(-disequality.constant))
    } else if (disequality.constants.size == 2 &&
               disequality.constant.isZero &&
               disequality.getCoeff(0).isOne &&
               disequality.getCoeff(1).isMinusOne) {
      split(disequality.getTerm(0), disequality.getTerm(1))
    } else {
      //println("WARNING: cannot split " + disequality)
      List()
    }
  }

  private def splitExtractActions(extracts : Seq[Atom],
                                  partitions : Map[Term, List[Int]],
                                  goal : Goal)
                                 (implicit order : TermOrder)
                                : Seq[Plugin.Action] =
    for (ex <- extracts;
         action <- ex(2) match {
           case SingleTerm(c : ConstantTerm) =>
             splitExtract(ex, partitions(c))
           case _ =>
             List()
         }) 
    yield action

  /**
   * Splitting of disequalities x != N or x != y
   */
  private def splitDisequalityActions(disequalities : Seq[LinearCombination],
                                      partitions : Map[Term, List[Int]],
                                      goal : Goal)
                                     (implicit order : TermOrder)
                                    : Seq[Plugin.Action] =
    for (diseq <- disequalities;
         lhs = diseq(0)._2;
         parts <- (partitions get lhs).toSeq;
         action <- splitDiseq(diseq, parts, goal))
    yield action

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Replace negated predicates with positive predicates
   */
  private def negPreds(goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val negPreds1 =
      goal.facts.predConj.negativeLitsWithPred(_mod_cast) ++
      goal.facts.predConj.negativeLitsWithPred(_l_shift_cast)

    val actions1 =
      if (!negPreds1.isEmpty) {
        (for (a <- negPreds1) yield {
          val axiom =
            exists(Atom(a.pred, a.init ++ List(l(v(0))), order) &
              (v(0) >= a(0)) & (v(0) <= a(1)) & (v(0) =/= a.last))
          Plugin.AddAxiom(List(!conj(a)), axiom, ModuloArithmetic)
        }) ++ List(Plugin.RemoveFacts(conj(
                            for (a <- negPreds1) yield !conj(a))))
      } else {
        List()
      }

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

    actions1 ++ actions2
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

    castActions ++ extractActions
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

    println
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
