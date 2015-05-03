/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.proof.goal

import ap.basetypes.IdealInt
import ap.parameters.Param
import ap.proof.tree.{ProofTreeFactory, ProofTree}
import ap.terfor.equations.EquationConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.proof.certificates.{Certificate,
                              PartialCertificate, StrengthenCertificate,
                              CertInequality, CertEquation, CertFormula}
import ap.util.Debug

object BoundStrengthenTask {
  
  val AC = Debug.AC_COMPLEX_FORMULAS_TASK
  
}

/**
 * Task responsible for strengthening the inequalities <code>lc + b1 >= 0</code>
 * and <code>-lc - b2 >= 0</code> to <code>lc + b1 >= 1</code> and
 * <code>-lc - b2 >= 1</code>, introducing one splinter
 */
class BoundStrengthenTask(lc : LinearCombination, age : Int)
      extends PrioritisedTask {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(BoundStrengthenTask.AC, lc.constant.isZero)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
        
  val priority : Int = lc.size + age
 
  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val order = goal.order
    val inEqs = goal.facts.arithConj.inEqs
    
    val (lowerBoundEq, lowerBoundLC) = (inEqs findLowerBound lc) match {
      case None =>
        (Conjunction.TRUE, null)
      case Some(b) => {
        val boundLC = lc + (-b)
        (Conjunction.conj(EquationConj(boundLC, order), order),
         boundLC)
      }
    }
    
    val (upperBoundEq, upperBoundLC) = (inEqs findLowerBound -lc) match {
      case None =>
        (Conjunction.TRUE, null)
      case Some(b) => {
        val boundLC = lc + b
        (Conjunction.conj(EquationConj(boundLC, order), order),
         boundLC)
      }
    }
    
    val relevantPredicates =
      for (eq <- List(lowerBoundEq, upperBoundEq).distinct;
           if (!eq.isTrue)) yield eq
    
    relevantPredicates match {
      case List() =>
        // the specified linear combination is not relevant for the goal anymore
        ptf.updateGoal(goal)
      case List(eq) => {
        val weakInEq =
          if (lowerBoundLC == null)
            CertInequality(-upperBoundLC)
          else
            CertInequality(lowerBoundLC)

        val newInEqLC = weakInEq.lhs + IdealInt.MINUS_ONE
        val newInEq = Conjunction.conj(InEqConj(newInEqLC, order), order)

        val goal1 = ptf.updateGoal(goal formulaTasks eq.negate,
                                   goal startNewInferenceCollectionCert
                                          List(CertEquation(weakInEq.lhs)),
                                   goal)
        val goal2 = ptf.updateGoal(goal formulaTasks newInEq.negate,
                                   goal startNewInferenceCollectionCert
                                          List(CertInequality(newInEqLC)),
                                   goal)

        if (Param.PROOF_CONSTRUCTION(goal.settings)) {
          val branchInferences = goal.branchInferences
    
          def pCertFunction(children : Seq[Certificate]) : Certificate = {
            val strengthenCert =
              StrengthenCertificate(weakInEq, IdealInt.ONE, children, order)
            branchInferences.getCertificate(strengthenCert, order)
          }
          
          ptf.and(Array(goal1, goal2),
                  PartialCertificate(pCertFunction _, 2),
                  goal.vocabulary)

        } else {

          val goal1 = ptf.updateGoal(goal formulaTasks eq.negate, goal)
          val goal2 = ptf.updateGoal(goal formulaTasks eq, goal)
          ptf.and(Array(goal1, goal2), goal.vocabulary)

        }
      }

      case List(eq1, eq2) => {
        if (Param.PROOF_CONSTRUCTION(goal.settings)) {
          val negUpperBoundLC = -upperBoundLC

          val goal1 = ptf.updateGoal(goal formulaTasks eq1.negate,
                                     goal startNewInferenceCollectionCert
                                            List(CertEquation(lowerBoundLC)),
                                     goal)
          val goal2 = ptf.updateGoal(goal formulaTasks eq2.negate,
                                     goal startNewInferenceCollectionCert
                                            List(CertEquation(negUpperBoundLC)),
                                     goal)

          val newLowerInEqLC = lowerBoundLC + IdealInt.MINUS_ONE
          val newLowerInEq =
            Conjunction.conj(InEqConj(newLowerInEqLC, order), order)
          val newUpperInEqLC = negUpperBoundLC + IdealInt.MINUS_ONE
          val newUpperInEq =
            Conjunction.conj(InEqConj(newUpperInEqLC, order), order)

          val goal3 = ptf.updateGoal((goal formulaTasks newLowerInEq.negate) ++
                                     (goal formulaTasks newUpperInEq.negate),
                                     goal startNewInferenceCollectionCert
                                            List(CertInequality(newLowerInEqLC),
                                                 CertInequality(newUpperInEqLC)),
                                     goal)

          val branchInferences = goal.branchInferences
    
          def pCertFunction(children : Seq[Certificate]) : Certificate = {
            val upperStrengthenCert =
              StrengthenCertificate(CertInequality(negUpperBoundLC),
                                    IdealInt.ONE, children.tail, order)
            val lowerStrengthenCert =
              StrengthenCertificate(CertInequality(lowerBoundLC),
                                    IdealInt.ONE,
                                    List(children.head, upperStrengthenCert),
                                    order)
            branchInferences.getCertificate(lowerStrengthenCert, order)
          }
          
          ptf.and(Array(goal1, goal2, goal3),
                  PartialCertificate(pCertFunction _, 3),
                  goal.vocabulary)

        } else {

          val goal1 = ptf.updateGoal(goal formulaTasks eq1.negate, goal)
          val goal2 = ptf.updateGoal(goal formulaTasks eq2.negate, goal)
          val goal3 = ptf.updateGoal(goal formulaTasks
                                       Conjunction.disj(Array(eq1, eq2), order),
                                     goal)
          ptf.and(Array(goal1, goal2, goal3), goal.vocabulary)

        }
      }
    }
  }

  /**
   * Update the task with possibly new information from the goal. If new facts
   * can be derived, these are put into <code>factCollector</code>
   */
  def updateTask(goal : Goal,
                 factCollector : Conjunction => Unit) : Seq[PrioritisedTask] =
    // we do not update anything in this task; if no inequalities for the
    // specified linear combination occur in the goal anymore, we will just
    // ignore the task when it is to be applied
    List(this)

  
  override def toString : String =
    "BoundStrengthenTask(" + priority + ", " + lc  + ")"
}
