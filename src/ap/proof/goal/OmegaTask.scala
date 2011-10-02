/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.goal;

import ap.proof._
import ap.basetypes.IdealInt
import ap.parameters.{GoalSettings, Param}
import ap.terfor.{Term, TermOrder, ConstantTerm, OneTerm}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier}
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.arithconj.{ArithConj, ModelFinder}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs, PlainRange, FilterIt, IdealRange}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.{Certificate, PartialCertificate, SplitEqCertificate,
                              AntiSymmetryInference, BranchInferenceCertificate,
                              StrengthenCertificate, OmegaCertificate, CertInequality,
                              CertEquation, CertFormula}

import scala.collection.mutable.ArrayBuffer

/**
 * Task for eliminating inequalities using the equivalence from the Omega-test
 */
case object OmegaTask extends EagerTask {
  private val AC = Debug.AC_OMEGA

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val ac = goal.facts.arithConj
    val order = goal.order
    
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
    Debug.assertPre(AC, Seqs.disjoint(goal.eliminatedConstants,
                                      goal.tasks.taskInfos.constants))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val ec = eliminableConsts(goal)
    val store = new BestSplitPossibilityStore
    
    findOmegaPossibilities(goal, ptf, ec, store)
    for (n <- store.currentCases)
      if (n <= 1)
        // that's good enough
        return store.currentBest()
    
    val formulaSplitStore = new BestSplitPossibilityStore
    findFormulaSplitPossibilities(goal, ptf, ec, formulaSplitStore)
    store push formulaSplitStore
    
    if (store.currentCases == None)
      // the best case: there are no inequalities that have to be eliminated
      return ptf updateGoal goal

    findSplitInEqsPossibilities(goal, ptf, ec, store)
    
    if (goal.constants subsetOf goal.eliminatedConstants) {
      // this is just a satisfiability-problem
      
      if (store.currentCases.get > 50 && formulaSplitStore.currentCases == None &&
          !Param.PROOF_CONSTRUCTION(goal.settings)) {
        // If there are so many cases that the situation seems hopeless, and
        // all constants are to be eliminated, we instead split random
        // inequalities with a non-unit leading coefficient. This yields a
        // complete procedure for quantifier-free Presburger arithmetic, and is
        // guaranteed to find a countermodel if the goal is invalid (i.e.,
        // termination is guaranteed)
      
        // TODO: we need a more efficient complete method to check
        // unsatisfiability over the rationals at this point
        return (if (ac.inEqs.isRationallyFalse(goal.age))
                  ptf.updateGoal(Conjunction.FALSE, goal)
                else
                  strengthenInEqs(goal, ptf))
      }
      
    } else {
      
      // the following test seems to slow down Princess when all constants are
      // to be eliminated, but it is a good idea in general
      findBoundedConstantsFast(goal, ptf, ec, store)

// commented out, because it can make the prover loop in some (seldom) cases
//
//      if (store.currentCases.get > 50)
        // try the more expensive method to find a splitting possibility
//        findBoundedConstants(goal, ptf, ec, store)
      
    }
    
    store.currentBest()
  }

  private def eliminableConsts(goal : Goal) : Set[ConstantTerm] =
    goal.eliminatedConstants --
    goal.facts.predConj.constants --
    goal.compoundFormulas.constantsInMatchedClauses
  
  /**
   * Determine whether this task might causes proof splitting
   */
  def splittingNecessary(goal : Goal) : Boolean = {
    val ac = goal.facts.arithConj
    !Seqs.disjoint(ac.inEqs.constants, eliminableConsts(goal))
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
          def apply : ProofTree = whatToDo
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
      
      val lowerSplittingNum = predictOmegaSplitting(elimConst, lowerBounds, upperBounds)
      val upperSplittingNum = predictOmegaSplitting(elimConst, upperBounds, lowerBounds)
      
      val lowerSplitting = lowerSplittingNum <= upperSplittingNum
      
      store.push(if (lowerSplitting) lowerSplittingNum else upperSplittingNum) {
        val newGoals = new ArrayBuffer[ProofTree]
        val (boundsA, boundsB) = if (lowerSplitting)
                                   (lowerBounds, upperBounds)
                                 else
                                   (upperBounds, lowerBounds)
        
        // the splinters
        for (lc <- splinterEqs(elimConst, boundsA, boundsB, order)) {
          val newTasks =
            goal formulaTasks Conjunction.conj(NegEquationConj(lc, order), order)
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
        val darkShadowFors = if (Param.PROOF_CONSTRUCTION(goal.settings))
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
            // We have to make sure that the Omega task is repeated if there are
            // inequalities left. To ensure this, we simply add the remaining
            // inequalities as a task if the dark shadow is trivial
            List(remainder)
          else
            darkShadowFors

        val newTasks =
          for (f <- newFormulas;
               t <- goal.formulaTasks(Conjunction.conj(f, order).negate))
          yield t

        val darkShadowGoal = ptf.updateGoal(goal.facts.updateInEqs(remainder)(order),
                                            newTasks, newCollector.getCollection,
                                            goal)
        
        // we add a <code>ModelFinder</code> so that a witness for the eliminated
        // constant can be constructed
        val eliminatedInEqs =
          ArithConj.conj(InEqConj(lowerBounds.iterator ++ upperBounds.iterator,
                                  order), order)
        newGoals += ptf.eliminatedConstant(darkShadowGoal,
                                           elimConst,
                                           new ModelFinder (eliminatedInEqs, elimConst),
                                           goal.vocabulary)

        if (Param.PROOF_CONSTRUCTION(goal.settings)) {
          val order = goal.order
          val branchInferences = goal.branchInferences
    
          def pCertFunction(children : Seq[Certificate]) : Certificate = {
            val betaCert =
              OmegaCertificate(elimConst,
                               for (b <- boundsA) yield CertInequality(b),
                               for (b <- boundsB) yield CertInequality(b),
                               children, order)
            branchInferences.getCertificate(betaCert, order)
          }
      
          ptf.and(newGoals, PartialCertificate(pCertFunction _, newGoals.size),
                  goal.vocabulary)
        } else {
          ptf.and(newGoals, goal.vocabulary)
        }
      }
    }
  }
  
  private def predictOmegaSplitting(elimConst : ConstantTerm,
                                    lowerBounds : Seq[LinearCombination],
                                    upperBounds : Seq[LinearCombination]) : IdealInt = {
    val m = IdealInt.max(for (lc <- upperBounds.iterator) yield (lc get elimConst).abs)
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
          val geqCoeff = (geq get elimConst).abs;
          val casesSucc = -(cases + IdealInt.ONE);
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
    for (lc <- lowerBounds.iterator; val coeff = (lc get elimConst).abs)
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

  private def findFormulaSplitPossibilitiesHelp(goal : Goal, ptf : ProofTreeFactory,
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
    val order = goal.order

    // We have to split the goal directly,
    // because when just adding a formula eq >= 0 & eq <= 0 this will
    // directly be simplified to an equation

    // TODO: directly remove the negated equation
    
    val lowerBoundInEq = InEqConj(eq, order)
    val lowerBound = Conjunction.conj(lowerBoundInEq, order)
    val upperBoundInEq = InEqConj(-eq, order)
    val upperBound = Conjunction.conj(upperBoundInEq, order)
    val goal1 = ptf.updateGoal(goal.formulaTasks(lowerBound),
                               goal.startNewInferenceCollection,
                               goal)
    val goal2 = ptf.updateGoal(goal.formulaTasks(upperBound),
                               goal.startNewInferenceCollection,
                               goal)
    
    if (Param.PROOF_CONSTRUCTION(goal.settings)) {
      val order = goal.order
      val branchInferences = goal.branchInferences
    
      val leftFormula = CertInequality(lowerBoundInEq.negate(0))
      val rightFormula = CertInequality(upperBoundInEq.negate(0))
      
      def pCertFunction(children : Seq[Certificate]) : Certificate = {
        val betaCert = SplitEqCertificate(leftFormula, rightFormula,
                                          children(0), children(1), order)
        branchInferences.getCertificate(betaCert, order)
      }
      
      ptf.and(Array(goal1, goal2),
              PartialCertificate(pCertFunction _,
                                 Array(Set(leftFormula).asInstanceOf[Set[CertFormula]],
                                       Set(rightFormula).asInstanceOf[Set[CertFormula]]),
                                 (branchInferences.getCertificate(_, order)),
                                 2),
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
    val order = goal.order

    var i = 0
    while (i < inEqs.size && (goal eliminates inEqs(i).leadingTerm)) {
      val lc = inEqs(i)
      if (lc.leadingCoeff.signum > 0 && !Seqs.disjoint(lc.constants, eConsts)) {
        inEqs.findLowerBound(-lc) match {
          case Some(negDistance) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, negDistance.signum < 0)
            //-END-ASSERTION-///////////////////////////////////////////////////
            
            val cases = -negDistance + 1
            store.push(cases) {
              val goals = for (d <- IdealRange(cases)) yield {
                val shiftedLC = lc + (-d)
                val newFacts = Conjunction.conj(NegEquationConj(shiftedLC, order), order)
                ptf.updateGoal(goal.formulaTasks(newFacts),
                               goal.startNewInferenceCollection, goal)
              }

              if (Param.PROOF_CONSTRUCTION(goal.settings)) {
                val order = goal.order
                val branchInferences = goal.branchInferences
    
                val weakInEq = CertInequality(lc)
                
                def pCertFunction(children : Seq[Certificate]) : Certificate = {
                  // in the last goal, we have to infer an equation from two
                  // complementary inequalities
                  val lastLC = lc + negDistance
                  val lastInf =
                    AntiSymmetryInference(CertInequality(lastLC),
                                          CertInequality(-lastLC),
                                          order)
                  val lastCert =
                    BranchInferenceCertificate(List(lastInf), children.last, order)
                  val allCerts =
                    children.take(children.size - 1) ++ List(lastCert)
                  val strengthenCert =
                    StrengthenCertificate(weakInEq, -negDistance,
                                          allCerts, order)
                  branchInferences.getCertificate(strengthenCert, order)
                }
      
                ptf.and(goals,
                        PartialCertificate(pCertFunction _, cases.intValueSafe),
                        goal.vocabulary)
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
  private def findBoundedConstantsFast(goal : Goal, ptf : ProofTreeFactory,
                                       eConsts : Set[ConstantTerm],
                                       store : BestSplitPossibilityStore) : Unit = {
    val ac = goal.facts.arithConj
    val order = goal.order

    val elimCandidates = (ac.inEqs.constants & eConsts)

    for (elimConst <- order sort elimCandidates) store.currentCases match {
      case Some(n) if (n <= 1) =>
        // nothing, we do not have to continue searching
      case _ => {
        
        // We change the order so that the constant to be eliminated is minimal.
        // The Fourier-Motzkin rule will then derive bounds for the constant
        
        val reOrder = order.makeMaximal(elimConst, order.orderedConstants - elimConst)
        val reorderedInEqs = ac.inEqs sortBy reOrder
      
        if (reorderedInEqs.isFalse) {
          // the the considered <code>ac</code> really is unsatisfiable, and we
          // can directly clorse the goal
          store.push(0) {
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
    val order = TermOrder.EMPTY.extend(x, Set()).extend(y, Set()).extend(c, Set())
    
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
