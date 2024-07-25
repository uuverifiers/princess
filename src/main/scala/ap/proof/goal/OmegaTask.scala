/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal;

import ap.proof._
import ap.basetypes.IdealInt
import ap.parameters.{GoalSettings, Param}
import ap.terfor.{Term, TermOrder, ConstantTerm, OneTerm}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier}
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.arithconj.{ArithConj, InNegEqModelElement}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs, PlainRange, FilterIt, IdealRange, Timeout}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.{Certificate, PartialCertificate, SplitEqCertificate,
                              AntiSymmetryInference, BranchInferenceCertificate,
                              StrengthenCertificate, StrengthenCertificateHelper,
                              OmegaCertificate, CertInequality,
                              CertEquation, CertFormula, BranchInferenceCollection}

import ap.theories.nia.IntervalPropagator

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}

/**
 * Task for eliminating inequalities using the equivalence from the Omega-test
 */
case object OmegaTask extends EagerTask {
  private val AC = Debug.AC_OMEGA

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private val debug = false
  private def printDebug(msg : String) = if (debug) println(msg)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val ac = goal.facts.arithConj
    val order = goal.order

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    printDebug("========================================================")
    printDebug("Calling Omega")
    printDebug("Inequalities: " + ac.inEqs.size)
    printDebug("Constants:    " + goal.facts.constants.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (!Seqs.disjoint(goal.eliminatedConstants, ac.positiveEqs.constants)) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // the reason has to be that we are constructing a proof, and that certain
      // constants cannot be eliminated from arithmetic clauses
      Debug.assertPre(AC, Param.PROOF_CONSTRUCTION(goal.settings))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      if (Seqs.disjoint(goal.eliminatedConstants,
                        ac.positiveEqs.constants,
                        goal.compoundFormulas.qfClauses.constants)) {
        // we cannot eliminate all constants due to quantified formula and
        // don't do any Omega splitting for the time being

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, !Seqs.disjoint(goal.eliminatedConstants,
                                           ac.positiveEqs.constants,
                                           goal.compoundFormulas.constants))
        //-END-ASSERTION-///////////////////////////////////////////////////////

        return ptf updateGoal goal

      } else {
        
        // In this case, we can split an arithmetic clause
      
        val store = new BestSplitPossibilityStore
        val leadingConstants = Set() ++
          (for (Seq((_, c : ConstantTerm), _*) <- ac.positiveEqs.iterator)
              yield c)
        findFormulaSplitPossibilitiesHelp(goal, ptf, leadingConstants, store)
      
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, store.currentCases != None)
        //-END-ASSERTION-///////////////////////////////////////////////////////
      
        return store.currentBest()
      }
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // OmegaTask should be the last remaining task to be done
//    Debug.assertPre(AC, Seqs.disjoint(goal.eliminatedConstants,
//                                      goal.tasks.taskConstants))
    Debug.assertPre(AC, goal.tasks.prioritisedTasks forall {
                      case _ : BlockedFormulaTask => true
                      case _ => false
                    })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val ec = eliminableOmegaConsts(goal)
    val store = new BestSplitPossibilityStore
    
    findOmegaPossibilities(goal, ptf, ec, store)
    for (n <- store.currentCases)
      if (n <= 1)
        // just a single case, we can directly apply this rule
        return store.currentBest()
    
    val formulaSplitStore = new BestSplitPossibilityStore
    findFormulaSplitPossibilities(goal, ptf,
                                  goal.eliminatedConstants,
                                  formulaSplitStore)
    store push formulaSplitStore
    
    store.currentCases match {
      case None =>
        // the best case: there are no inequalities that have to be eliminated
        return ptf updateGoal goal
      case Some(n) =>
        if (n <= 5)
          return store.currentBest()
    }

    findSplitInEqsPossibilities(goal, ptf, goal.eliminatedConstants, store)

//    if (!Param.PROOF_CONSTRUCTION(goal.settings))
//      findBoundedConstantsICP(goal, ptf, goal.eliminatedConstants, store)

    if (store.currentCases.get > 1000 &&
        formulaSplitStore.currentCases == None &&
        (goal.constants subsetOf goal.eliminatedConstants)) {
      // This is just a satisfiability-problem.
      // If there are so many cases that the situation seems hopeless, and
      // all constants are to be eliminated, we instead split random
      // inequalities with a non-unit leading coefficient. This yields a
      // complete procedure for quantifier-free Presburger arithmetic, and is
      // guaranteed to find a countermodel if the goal is invalid (i.e.,
      // termination is guaranteed)

      return strengthenInEqs(goal, ptf)
    }

/*
    if (goal.constants subsetOf goal.eliminatedConstants) {
      // this is just a satisfiability-problem
      
      if (store.currentCases.get > 5000 &&
          formulaSplitStore.currentCases == None) {
        // If there are so many cases that the situation seems hopeless, and
        // all constants are to be eliminated, we instead split random
        // inequalities with a non-unit leading coefficient. This yields a
        // complete procedure for quantifier-free Presburger arithmetic, and is
        // guaranteed to find a countermodel if the goal is invalid (i.e.,
        // termination is guaranteed)

        // TODO: we need a more efficient complete method to check
        // unsatisfiability over the rationals at this point
        return (if (!Param.PROOF_CONSTRUCTION(goal.settings) &&
                    ac.inEqs.isRationallyFalse(goal.age))
                  ptf.updateGoal(Conjunction.FALSE, goal)
                else
                  strengthenInEqs(goal, ptf))
      }
      
    } else {

// commented out, because it can make the prover loop in some (seldom) cases
//
//      if (store.currentCases.get > 50)
        // try the more expensive method to find a splitting possibility
//        findBoundedConstants(goal, ptf, ec, store)
      
    }
  */
  
    store.currentBest()
  }

  /**
   * Determine constants that can be eliminated through the Omega rule
   */
  private def eliminableOmegaConsts(goal : Goal) : Set[ConstantTerm] =
    goal.eliminatedConstants --
    goal.facts.predConj.constants --
    goal.compoundFormulas.constantsInMatchedClauses
  
  /**
   * Determine whether this task might causes proof splitting
   */
  def splittingNecessary(goal : Goal) : Boolean = {
    val ac = goal.facts.arithConj
    !Seqs.disjoint(ac.inEqs.constants, goal.eliminatedConstants)
  }
    
  //////////////////////////////////////////////////////////////////////////////

  private abstract class SplitPossibility extends (() => ProofTree) {
    /**
     * A prediction for the number of cases that choosing this possibility will
     * (eventually) lead to
     */
    val cases : IdealInt
  }

  private class BestSplitPossibilityStore {
    var currentBest : SplitPossibility = null
    
    def currentCases : Option[IdealInt] =
      if (currentBest == null)
        None
      else
        Some(currentBest.cases)
    
    def push(newCases : IdealInt)(whatToDo : => ProofTree) : Unit =
      if (currentBest == null || currentBest.cases > newCases)
        currentBest = new SplitPossibility {
          val cases = newCases
          def apply() : ProofTree = whatToDo
        }
    
    def push(that : BestSplitPossibilityStore) : Unit =
      (this.currentCases, that.currentCases) match {
        case (_, None) => // nothing
        case (Some(c), Some(d)) if (c <= d) => // nothing
        case _ => this.currentBest = that.currentBest
      }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find all possible applications of the Omega rule to this sequent
   */
  private def findOmegaPossibilities(goal : Goal, ptf : ProofTreeFactory,
                                     eConsts : Set[ConstantTerm],
                                     store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val order = goal.order

    val elimCandidates = (ac.inEqs.constants & eConsts) --
                         ac.negativeEqs.constants --
                         goal.compoundFormulas.constants
    
    for (elimConst <- order sort elimCandidates) {
      // select inequalities that contain c
      val lowerBounds = new ArrayBuffer[LinearCombination]        
      val upperBounds = new ArrayBuffer[LinearCombination]        
      val remainingInEqs = new ArrayBuffer[LinearCombination]
        
      for (lc <- ac.inEqs) {
        (lc get elimConst).signum match {
          case 0  => remainingInEqs += lc
          case 1  => lowerBounds += lc
          case -1 => upperBounds += lc
        }
      }
      
      val lowerSplittingNum =
        predictOmegaSplitting(elimConst, lowerBounds, upperBounds)
      val upperSplittingNum =
        predictOmegaSplitting(elimConst, upperBounds, lowerBounds)
      
      val lowerSplitting =
        lowerSplittingNum <= upperSplittingNum
      val splittingNum =
        if (lowerSplitting) lowerSplittingNum else upperSplittingNum

      // The Omega rule can explode for two reasons: too many cases are
      // generated, or too many inequalities are created in the dark shadow.
      // We take the average of the two numbers to reflect this.

      val lbSize =     IdealInt(lowerBounds.size)
      val ubSize =     IdealInt(upperBounds.size)
      val ineqGrowth = (lbSize * ubSize) - lbSize - ubSize

      store.push((splittingNum + (ineqGrowth max 1)) / 2) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        printDebug("Applying Omega rule")
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val allBounds = lowerBounds ++ upperBounds

        if (Param.PROOF_CONSTRUCTION(goal.settings) && splittingNum.isOne) {
          //////////////////////////////////////////////////////////////////////
          // This means that we can directly compute the exact shadow, and do
          // not need the full Omega rule at all

          val collector = goal.getInferenceCollector
          val (eliminated, shadowLCs) =
            InEqConj.exactShadow(elimConst, allBounds, collector, order)

          val remainingInEq =
            InEqConj(remainingInEqs.iterator, collector, order)
          val darkShadowFacts =
            goal.facts.updateInEqs(remainingInEq)(order)
          val newTasks =
            for (lc <- shadowLCs;
                 c = Conjunction.negate(InEqConj(lc, order), order);
                 t <- goal formulaTasks c)
            yield t

          val shadowGoal =
            ptf.updateGoal(darkShadowFacts,
                           newTasks,
                           collector.getCollection,
                           goal)

          // we add a <code>ModelFinder</code> so that a witness for the
          // eliminated constant can be constructed
          val eliminatedInEqs =
            ArithConj.conj(InEqConj(allBounds, order), order)
          ptf.eliminatedConstant(shadowGoal,
                                 InNegEqModelElement(eliminatedInEqs,
                                                     elimConst),
                                 goal.vocabulary)

        } else {
          //////////////////////////////////////////////////////////////////////
          // Otherwise, use the full Omega rule

          val newGoals = new ArrayBuffer[ProofTree]
          val (boundsA, boundsB) = if (lowerSplitting)
                                     (lowerBounds, upperBounds)
                                   else
                                     (upperBounds, lowerBounds)
        
          // the splinters
          for (lc <- splinterEqs(elimConst, boundsA, boundsB, order)) {
            val newTasks =
              goal formulaTasks Conjunction.conj(NegEquationConj(lc, order),
                                                 order)
            val newCollection =
              goal startNewInferenceCollectionCert List(CertEquation(lc))
            
            newGoals += ptf.updateGoal(newTasks, newCollection, goal)
          }
        
          // the dark shadow
          val darkShadowInEqs = darkShadow(elimConst, boundsA, boundsB, order)
        
          /**
           * If proofs are constructed, the dark shadow inequalities are added
           * one by one; otherwise, we create a big conjunction first
           */
          val darkShadowFors =
            if (Param.PROOF_CONSTRUCTION(goal.settings))
              for (lc <- darkShadowInEqs) yield InEqConj(lc, order)
            else
              List(InEqConj(darkShadowInEqs, order))

          val newCollector =
            goal.startNewInferenceCollectionCert(
                   for (lc <- darkShadowInEqs) yield CertInequality(lc))
                .getCollector

          val remainder = InEqConj(remainingInEqs.iterator, newCollector, order)

          val newFormulas =
            if (darkShadowFors forall (_.isTrue))
              // We have to make sure that the Omega task is repeated if there
              // are
              // inequalities left. To ensure this, we simply add the remaining
              // inequalities as a task if the dark shadow is trivial
              List(remainder)
            else
              darkShadowFors

          val newTasks =
            for (f <- newFormulas;
                 t <- goal.formulaTasks(Conjunction.conj(f, order).negate))
            yield t

          val darkShadowFacts = goal.facts.updateInEqs(remainder)(order)
          val darkShadowGoal  = ptf.updateGoal(darkShadowFacts,
                                               newTasks,
                                               newCollector.getCollection,
                                               goal)
        
          newGoals +=
           (if (darkShadowFacts.isFalse) {
              darkShadowGoal
            } else {
              // we add a <code>ModelFinder</code> so that a witness for the
              // eliminated constant can be constructed
              val eliminatedInEqs =
                ArithConj.conj(InEqConj(allBounds, order), order)
              ptf.eliminatedConstant(darkShadowGoal,
                                     InNegEqModelElement(eliminatedInEqs,
                                                         elimConst),
                                     goal.vocabulary)
            })
                                             
          if (Param.PROOF_CONSTRUCTION(goal.settings)) {
            val order = goal.order

            val boundsAInEqs = for (b <- boundsA) yield CertInequality(b)
            val boundsBInEqs = for (b <- boundsB) yield CertInequality(b)

            def pCertFunction(children : Seq[Certificate]) : Certificate =
              OmegaCertificate(elimConst, boundsAInEqs, boundsBInEqs,
                               children, order)

            val providedFormulas =
              OmegaCertificate.providedFormulas(
                                 elimConst,
                                 boundsAInEqs, boundsBInEqs, order,
                                 OmegaCertificate.strengthenCases(
                                   elimConst, boundsAInEqs, boundsBInEqs))
            val pCert =
              PartialCertificate(pCertFunction _,
                                 providedFormulas,
                                 goal.branchInferences,
                                 order)

            ptf.and(newGoals, pCert, goal.vocabulary)
          } else {
            ptf.and(newGoals, goal.vocabulary)
          }
        }
      }
    }
  }
  
  private def predictOmegaSplitting(
                 elimConst : ConstantTerm,
                 lowerBounds : Seq[LinearCombination],
                 upperBounds : Seq[LinearCombination]) : IdealInt = {
    val m = IdealInt.max(for (lc <- upperBounds.iterator)
                         yield (lc get elimConst).abs)
    (IdealInt.ONE /: 
       (for (lc <- lowerBounds.iterator) yield {
          val coeff = (lc get elimConst).abs
          ((m - IdealInt.ONE) * coeff - m) / m + IdealInt.ONE
        })) (_ + _)
  }
   
  /**
   * Generate the dark shadow (i.e., a conjunction of inequalities). The method
   * also can be called with swapped <code>lowerBounds</code>/
   * <code>upperBounds</code>, depending on which bounds are supposed to be
   * strengthened
   */
  private def darkShadow(elimConst : ConstantTerm,
                         lowerBounds : Seq[LinearCombination],
                         upperBounds : Seq[LinearCombination],
                         order : TermOrder) : Seq[LinearCombination] =
    (for ((geq, cases) <- lowerBounds.iterator zip
                          strengthenCases(elimConst, lowerBounds, upperBounds);
          geqCoeff = (geq get elimConst).abs;
          casesSucc = -(cases + IdealInt.ONE);
          leq <- upperBounds.iterator) yield {
       val leqCoeff = (leq get elimConst).abs
       val correction = casesSucc * leqCoeff // always negative

       LinearCombination.sum(leqCoeff, geq,
                             geqCoeff, leq,
                             correction, LinearCombination.ONE,
                             order)
    }).toList

  /**
   * Generate the equations that describe the splinters.
   */
  private def splinterEqs(elimConst : ConstantTerm,
                          lowerBounds : Seq[LinearCombination],
                          upperBounds : Seq[LinearCombination],
                          order : TermOrder) : Iterator[LinearCombination] =
    for ((lc, cases) <- lowerBounds.iterator zip
                        strengthenCases(elimConst, lowerBounds, upperBounds);
         k <- IdealRange(cases + 1).iterator)
    yield (lc + (-k))

  private def strengthenCases(elimConst : ConstantTerm,
                              lowerBounds : Seq[LinearCombination],
                              upperBounds : Seq[LinearCombination])
                             : Iterator[IdealInt] = {
    val m =
      IdealInt.max(for (lc <- upperBounds.iterator) yield (lc get elimConst).abs)
    for (lc <- lowerBounds.iterator; coeff = (lc get elimConst).abs)
      yield (((m - IdealInt.ONE) * coeff - m) / m)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find all possible cases of equations in the succedent and of compound
   * formulas that eventually have to be split
   */
  private def findFormulaSplitPossibilities(goal : Goal, ptf : ProofTreeFactory,
                                            eConsts : Set[ConstantTerm],
                                            store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj

    // those constants are interesting that have to be eliminated and that occur
    // both in equations in the succedent and in inequalities, or that occur
    // in compound formulas and in inequalities
    val elimCandidates = ac.inEqs.constants & eConsts &
                         (ac.negativeEqs.constants ++
                          goal.compoundFormulas.qfClauses.constants)
   
    findFormulaSplitPossibilitiesHelp(goal, ptf, elimCandidates, store)
  }

  private def findFormulaSplitPossibilitiesHelp(
                goal : Goal, ptf : ProofTreeFactory,
                elimCandidates : Set[ConstantTerm],
                store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val order = goal.order
    
    for (elimConst <- order sort elimCandidates) {
      val eqs =
        ac.negativeEqs filter (_.constants contains elimConst)
      val clauses =
        goal.compoundFormulas.qfClauses filter (_.constants contains elimConst)
      
      // in the worst case, we have to split each of the equations and
      // compound formulas
      store.push(IdealInt(2) pow (eqs.size + clauses.size)) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        printDebug("Splitting formula")
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (clauses.isEmpty)
          splitEq(eqs.last, goal, ptf)
        else
          splitClause(clauses.head, elimConst, goal, ptf)
      }
    }
  }
  
  /**
   * Split a clause in order to isolate eliminated constants that occur in
   * inequalities
   */
  private def splitClause(c : Conjunction,
                          isolatedConstant : ConstantTerm,
                          goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    var selectedConjunct : Conjunction = null 
    val otherConjuncts = new ArrayBuffer[Conjunction]
    for (conjunct <- c.iterator) {
      if (selectedConjunct == null &&
          (conjunct.constants contains isolatedConstant))
        selectedConjunct = conjunct
      else
        otherConjuncts += conjunct
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, selectedConjunct != null)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // make sure that the clause is removed from the goal (might lead to
    // infinite loops otherwise)
    val oldQFClauses =
      goal.compoundFormulas.qfClauses
    val newQFClauses =
      NegatedConjunctions(FilterIt(oldQFClauses.iterator, c != ), goal.order)
    
    BetaFormulaTask.doSplit(selectedConjunct,
                            Conjunction.conj(otherConjuncts, goal.order),
                            goal.compoundFormulas updateQFClauses newQFClauses,
                            goal, ptf)
  }
  
  /**
   * Split an equation in the succedent into two inequalities
   */
  private def splitEq(eq : LinearCombination,
                      goal : Goal,
                      ptf : ProofTreeFactory) : ProofTree = {
    implicit val order = goal.order
    val facts = goal.facts
    val ac = facts.arithConj

    // We have to split the goal directly,
    // because when just adding a formula eq >= 0 & eq <= 0 this will
    // directly be simplified to an equation

    val remNegEqs =
      ac.negativeEqs.updateEqsSubset(ac.negativeEqs filterNot (_ == eq))
    val newFacts =
      facts.updateNegativeEqs(remNegEqs)

    val lowerBoundInEq = InEqConj(eq, order)
    val lowerBound =     Conjunction.conj(lowerBoundInEq, order)
    val upperBoundInEq = InEqConj(-eq, order)
    val upperBound =     Conjunction.conj(upperBoundInEq, order)
    val goal1 = ptf.updateGoal(newFacts,
                               goal.formulaTasks(lowerBound),
                               goal.startNewInferenceCollection,
                               goal)
    val goal2 = ptf.updateGoal(newFacts,
                               goal.formulaTasks(upperBound),
                               goal.startNewInferenceCollection,
                               goal)
    
    if (Param.PROOF_CONSTRUCTION(goal.settings)) {
      val order = goal.order
    
      val leftFormula = CertInequality(lowerBoundInEq.negate(0))
      val rightFormula = CertInequality(upperBoundInEq.negate(0))
      
      def pCertFunction(children : Seq[Certificate]) : Certificate =
        SplitEqCertificate(leftFormula, rightFormula,
                           children(0), children(1), order)
      
      ptf.and(Array(goal1, goal2),
              PartialCertificate(pCertFunction _,
                                 Array(Set(leftFormula)
                                         .asInstanceOf[Set[CertFormula]],
                                       Set(rightFormula)
                                         .asInstanceOf[Set[CertFormula]]),
                                 goal.branchInferences,
                                 order),
              goal.vocabulary)
    } else {
      ptf.and(Array(goal1, goal2), goal.vocabulary)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine whether there are pairs of inequalities of the form
   * <code> t >= 0 & t <= l</code> that could be split
   */
  private def findSplitInEqsPossibilities(goal : Goal, ptf : ProofTreeFactory,
                                          eConsts : Set[ConstantTerm],
                                          store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val inEqs = ac.inEqs
    val allGeqZero = inEqs.allGeqZero
    val order = goal.order

    var i = 0
    while (i < allGeqZero.size && (goal eliminates allGeqZero(i).leadingTerm)) {
      val lc = allGeqZero(i)
      if (lc.leadingCoeff.signum > 0 && !Seqs.disjoint(lc.constants, eConsts)) {
        inEqs.findLowerBound(-lc) match {
          case Some(negDistance) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, negDistance.signum < 0)
            //-END-ASSERTION-///////////////////////////////////////////////////
            
            val cases = -negDistance + 1
            store.push(cases) {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              printDebug("Enumerating inequality cases for " + lc +
                         " (" + cases + ")")
              //-END-ASSERTION-/////////////////////////////////////////////////
              val goals = for (d <- IdealRange(cases)) yield {
                Timeout.check
                val shiftedLC = lc + (-d)
                val newFacts = Conjunction.conj(NegEquationConj(shiftedLC, order), order)
                ptf.updateGoal(goal.formulaTasks(newFacts),
                               goal.startNewInferenceCollection, goal)
              }

              if (Param.PROOF_CONSTRUCTION(goal.settings)) {
                val order = goal.order
    
                val weakInEq = CertInequality(lc)

                def strengthenPCertFun(children : Seq[Certificate]) : Certificate =
                  StrengthenCertificate(weakInEq, -negDistance, children, order)

                val strengthenPCert =
                  PartialCertificate(strengthenPCertFun _,
                                     StrengthenCertificateHelper.providedFormulas(
                                       weakInEq, -negDistance, order),
                                     goal.branchInferences,
                                     order)

                // in the last goal, we have to infer an equation from two
                // complementary inequalities
                val lastLC = lc + negDistance
                val lastInf =
                  AntiSymmetryInference(CertInequality(lastLC),
                                        CertInequality(-lastLC),
                                        order)
                val lastInfColl =
                  BranchInferenceCollection(List(lastInf))
                
                val pCert =
                  strengthenPCert after {
                    (for (_ <- 1 until strengthenPCert.arity)
                     yield PartialCertificate.IDENTITY) ++
                    List(PartialCertificate(lastInfColl, order))
                  }

                ptf.and(goals, pCert, goal.vocabulary)
              } else {
                  ptf.and(goals, goal.vocabulary)
              }
            }
          }
          case None => // Nothing
        }
      }
      
      i = i + 1
    }
  }

  //////////////////////////////////////////////////////////////////////////////
 
  /**
   * Generate <code>BoundStrengthenTask</code>s to strengthen the inequalities
   * present in this goal
   */
  private def strengthenInEqs(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val ac = goal.facts.arithConj
    val order = goal.order

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(OmegaTask.AC, !ac.inEqs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newTasks =
      for (lc <- ac.inEqs.geqZero ++ ac.inEqs.geqZeroInfs)
          yield new BoundStrengthenTask(lc.-(LinearCombination(lc.constant))(order),
                                        goal.age)
    ptf.updateGoal(newTasks, goal)
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether we can find an eliminated symbol whose value is bounded (in
   * this case, we can just split over all possible values)
   */
  private def findBoundedConstantsICP(
                goal : Goal, ptf : ProofTreeFactory,
                eConsts : Set[ConstantTerm],
                store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val inEqs = ac.inEqs
    val order = goal.order

    val prop = IntervalPropagator(goal)

    for (elimConst <- order sort eConsts)
      for (lb <- prop lowerBound elimConst;
           ub <- prop upperBound elimConst)
        if (ub < lb) {
          // we found an inconsistency, the goal can be closed directly
          store.push(0) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printDebug("Closing goal")
            //-END-ASSERTION-///////////////////////////////////////////////////
            ptf.updateGoal(Conjunction.FALSE, goal)
          }
        } else {
          val cases = ub - lb + 1
          store.push(cases) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printDebug("Enumerating values for " + elimConst +
                       " (" + cases + ")")
            //-END-ASSERTION-///////////////////////////////////////////////////
            val goals = for (d <- IdealRange(cases)) yield {
              val lc =
                LinearCombination(IdealInt.ONE, elimConst, -(lb + d), order)
              val newFacts =
                Conjunction.conj(NegEquationConj(lc, order), order)
              ptf.updateGoal(goal.formulaTasks(newFacts), goal)
            }
              
            ptf.and(goals, goal.vocabulary)
          }
        }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether we can find an eliminated symbol whose value is bounded (in
   * this case, we can just split over all possible values)
   */
  private def findBoundedConstantsFast(
                goal : Goal, ptf : ProofTreeFactory,
                eConsts : Set[ConstantTerm],
                store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val inEqs = ac.inEqs
    val order = goal.order

    // We consider constants that have both lower and upper bounds
    val lower, upper = new MHashSet[ConstantTerm]
    for (lc <- inEqs.iterator; (coeff, c : ConstantTerm) <- lc.iterator)
      (if (coeff.signum > 0) lower else upper) += c

    val elimCandidates = lower.toSet & upper.toSet & eConsts

    for (elimConst <- order sort elimCandidates) store.currentCases match {
      case Some(n) if n <= 1 =>
        // nothing, we do not have to continue searching
      case _ => {

        // We change the order so that the constant to be eliminated is minimal.
        // The Fourier-Motzkin rule will then derive bounds for the constant
        
        val reOrder = order.makeMaximal(elimConst, order.orderedConstants - elimConst)
        val reorderedInEqs = inEqs sortBy reOrder
      
        if (reorderedInEqs.isFalse) {
          // the the considered <code>ac</code> really is unsatisfiable, and we
          // can directly close the goal
          store.push(0) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            printDebug("Closing goal")
            //-END-ASSERTION-///////////////////////////////////////////////////
            ptf.updateGoal(Conjunction.FALSE, goal)
          }
        } else {
          // check and compute a lower and an upper bound of the formula
        
          val lc = LinearCombination(elimConst, reOrder)
          for (lowerBound <- reorderedInEqs findLowerBound lc;
               negUpperBound <- reorderedInEqs findLowerBound -lc) {
            val upperBound = -negUpperBound
            val cases = upperBound - lowerBound + 1
            store.push(cases) {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              printDebug("Enumerating values for " + elimConst +
                         " (" + cases + ")")
              //-END-ASSERTION-/////////////////////////////////////////////////
              val goals = for (d <- IdealRange(cases)) yield {
                val lc =
                  LinearCombination(IdealInt.ONE, elimConst, -(lowerBound + d), order)
                val newFacts =
                  Conjunction.conj(NegEquationConj(lc, order), order)
                ptf.updateGoal(goal.formulaTasks(newFacts), goal)
              }
              
              ptf.and(goals, goal.vocabulary)
            }
          }
        }
      }
    }
    
  }

  /**
   * Check whether we can find an eliminated symbol whose value is bounded (in
   * this case, we can just split over all possible values)
   */
  private def findBoundedConstants(goal : Goal, ptf : ProofTreeFactory,
                                   eConsts : Set[ConstantTerm],
                                   store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val order = goal.order

    val elimCandidates = (ac.inEqs.constants & eConsts)
    
    for (elimConst <- order sort elimCandidates) {
      val boundFormula =
        Conjunction.quantify(Quantifier.EX,
                             order.sort(ac.constants -- Set(elimConst)),
                             ac, order)
      val qfBoundFormula =
        ConstraintSimplifier.FAIR_SIMPLIFIER(boundFormula, order)
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC,
                      (qfBoundFormula.constants subsetOf Set(elimConst)) &&
                      qfBoundFormula.predicates.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      if (qfBoundFormula.isFalse) {
        // the the considered <code>ac</code> really is unsatisfiable, and we
        // can directly clorse the goal
        store.push(0) {
          ptf.updateGoal(Conjunction.FALSE, goal)
        }
      } else if (!qfBoundFormula.isTrue) {
        // check and compute a lower and an upper bound of the formula
        for ((glb, lub) <- findBounds(elimConst, qfBoundFormula)) {
          val cases = lub - glb + 1
          store.push(cases) {
            val goals = for (d <- IdealRange(cases)) yield {
              val lc = LinearCombination(IdealInt.ONE, elimConst, -(glb + d), order)
              val newFacts = Conjunction.conj(NegEquationConj(lc, order), order)
              ptf.updateGoal(goal.formulaTasks(newFacts), goal)
            }
    
            ptf.and(goals, goal.vocabulary)
          }
        }
      }
    }
    
  }
  
  private def findBounds(c : ConstantTerm, cValFormula : Conjunction)
                                               : Option[(IdealInt, IdealInt)] = {
    val ac = cValFormula.arithConj
    if (!ac.positiveEqs.isTrue) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, cValFormula.isLiteral)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val bound = -ac.positiveEqs(0).constant
      return Some(bound, bound)
    } else if (!ac.inEqs.isTrue) {
      if (ac.inEqs.size == 2) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        ac.inEqs(0).leadingCoeff.isMinusOne &&
                        ac.inEqs(1).leadingCoeff.isOne)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return Some(-ac.inEqs(1).constant, ac.inEqs(0).constant)
      } else if (cValFormula.negatedConjs.isTrue) {
        return None
      }
    }
    
    for (glb <- findBound(c, cValFormula, false);
         lub <- findBound(c, cValFormula, true)) yield (glb, lub)
  }
  
  /**
   * Find a least upper or a greatest lower bound for the values of
   * <code>c</code> satisfying <code>cValFormula</code>. For simplicity,
   * this is done by constructing a Presburger formula and solving it using the 
   * normal prover (could be done faster ...):
   * <code>
   *   \forall c. phi(c) -> c >= x
   *     &
   *   \forall y. (\forall c. phi(c) -> c >= y) -> x >= y
   * </code>
   */
  private def findBound(c : ConstantTerm, cValFormula : Conjunction,
                        upper : Boolean) : Option[IdealInt] = {
    val x = new ConstantTerm ("x")
    val y = new ConstantTerm ("y")
    val order = TermOrder.EMPTY.extend(List(x, y, c))
    
    val one = if (upper) IdealInt.MINUS_ONE else IdealInt.ONE
    val minus_one = -one
    
    val cGeqX = InEqConj(LinearCombination(List((one, c), (minus_one, x)), order), order)
    val cGeqY = InEqConj(LinearCombination(List((one, c), (minus_one, y)), order), order)
    val xGeqY = InEqConj(LinearCombination(List((one, x), (minus_one, y)), order), order)
    
    val imp1 = Conjunction.quantify(Quantifier.ALL, List(c),
                                    Conjunction.implies(cValFormula, cGeqX, order),
                                    order)
    val imp2 = Conjunction.quantify(Quantifier.ALL, List(c),
                                    Conjunction.implies(cValFormula, cGeqY, order),
                                    order)
    val imp3 = Conjunction.quantify(Quantifier.ALL, List(y),
                                    Conjunction.implies(imp2, xGeqY, order), order)
    
    val boundFormula = Conjunction.conj(List(imp1, imp3), order)
    
    val bound = BOUND_PROVER(boundFormula, order).closingConstraint
    
    if (bound.isFalse) {
      None
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, bound.isLiteral && !bound.arithConj.positiveEqs.isTrue)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      Some(-bound.arithConj.positiveEqs(0).constant)
    }
  }
  
  private val BOUND_PROVER = new ExhaustiveProver(true, GoalSettings.DEFAULT)
  
  /*
  private def findBoundsXX(const : ConstantTerm,
                         boundFormula : Conjunction,
                         negated : Boolean) : Interval = {

    val ac = boundFormula.arithConj

    if (!ac.positiveEqs.isTrue) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, c.arithConj.positiveEqs.size == 1)
      //-END-ASSERTION-///////////////////////////////////////////////////////
      val bound = -c.arithConj.positiveEqs(0).constant
      Bounded(bound, bound)
    }
    
    for (c <- boundFormula.iterator) yield {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, c.constants == Set(const))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      if (!c.arithConj.positiveEqs.isTrue) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, c.arithConj.positiveEqs.size == 1)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val bound = -c.arithConj.positiveEqs(0).constant
        Bounded(bound, bound)
      } else if (!c.arithConj.negativeEqs.isTrue) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, c.arithConj.positiveEqs.size == 1)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val bound = -c.arithConj.positiveEqs(0).constant
        Bounded(bound, bound)
      }
        
    }
                           
    val ac = boundFormula.arithConj
    null
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Simple abstract domain of intervals, providing unions and intersections
   */
  private abstract class Interval {
    /**
     * Union of two intervals (overappproximation)
     */
    def +(that : Interval) : Interval = (this, that) match {
      case (Unbounded, _) | (_, Unbounded) =>
        Unbounded
      case (Empty, x) =>
        x
      case (x, Empty) =>
        x
      case (LowerBounded(b1), LowerBounded(b2)) =>
        LowerBounded(b1 min b2)
      case (UpperBounded(b1), UpperBounded(b2)) =>
        UpperBounded(b1 max b2)
      case (LowerBounded(_), UpperBounded(_)) | (UpperBounded(_), LowerBounded(_)) =>
        Unbounded
      case (LowerBounded(b1), Bounded(b2, _)) =>
        LowerBounded(b1 min b2)
      case (Bounded(b2, _), LowerBounded(b1)) =>
        LowerBounded(b1 min b2)
      case (UpperBounded(b1), Bounded(_, b3)) =>
        UpperBounded(b1 max b3)
      case (Bounded(_, b3), UpperBounded(b1)) =>
        UpperBounded(b1 max b3)
      case (Bounded(b1, b2), Bounded(b3, b4)) =>
        Bounded(b1 min b3, b2 max b4)
    }
    /**
     * Intersection of two intervals (overappproximation)
     */
    def *(that : Interval) : Interval = (this, that) match {
      case (Empty, _) | (_, Empty) =>
        Empty
      case (Unbounded, x) =>
        x
      case (x, Unbounded) =>
        x
      case (LowerBounded(b1), LowerBounded(b2)) =>
        LowerBounded(b1 max b2)
      case (UpperBounded(b1), UpperBounded(b2)) =>
        UpperBounded(b1 min b2)
      case (LowerBounded(b1), UpperBounded(b2)) =>
        if (b1 <= b2)
          Bounded(b1, b2)
        else
          Empty
      case (a : UpperBounded, b : LowerBounded) =>
        b * a
      case (LowerBounded(b1), Bounded(b2, b3)) => {
        val newLB = b1 max b2
        if (newLB <= b3)
          Bounded(newLB, b3)
        else
          Empty
      }
      case (a : Bounded, b : LowerBounded) =>
        b * a
      case (UpperBounded(b1), Bounded(b2, b3)) => {
        val newUB = b1 min b3
        if (b2 <= newUB)
          Bounded(b2, newUB)
        else
          Empty
      }
      case (a : Bounded, b : UpperBounded) =>
        b * a
      case (Bounded(b1, b2), Bounded(b3, b4)) => {
        val newLB = b1 max b3
        val newUB = b2 min b4
        if (newLB <= newUB)
          Bounded(newLB, newUB)
        else
          Empty
      }
    }
  }
  private case object Unbounded extends Interval
  private case object Empty extends Interval
  private case class LowerBounded(bound : IdealInt) extends Interval
  private case class UpperBounded(bound : IdealInt) extends Interval
  private case class Bounded(lower : IdealInt, upper : IdealInt) extends Interval {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC, lower <= upper)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  }
  */
}
