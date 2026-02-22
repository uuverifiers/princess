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

package ap.proof.goal

import ap.terfor.TermOrder
import ap.basetypes.IdealInt
import ap.parameters.Param
import ap.proof.tree.{ProofTreeFactory, ProofTree}
import ap.terfor.equations.EquationConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.proof.certificates.{Certificate,
                              PartialCertificate, StrengthenCertificate,
                              StrengthenCertificateHelper,
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
    
    (relevantPredicates: @unchecked) match {
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
          ptf.and(Array(goal1, goal2),
                  strengthenPCert(weakInEq, order).andThen(goal.branchInferences, order),
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

          val upperPCert =
            strengthenPCert(CertInequality(negUpperBoundLC), order)
          val lowerPCert =
            strengthenPCert(CertInequality(lowerBoundLC), order)
          val combinedPCert =
            lowerPCert after List(PartialCertificate.IDENTITY, upperPCert)

          ptf.and(Array(goal1, goal2, goal3),
                  combinedPCert.andThen(goal.branchInferences, order),
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

  private def strengthenPCert(weakInEq : CertInequality, order : TermOrder) = {
    def pCertFunction(children : Seq[Certificate]) : Certificate =
      StrengthenCertificate(weakInEq, IdealInt.ONE, children, order)
          
    PartialCertificate(pCertFunction _,
                       StrengthenCertificateHelper.providedFormulas(
                         weakInEq, IdealInt.ONE, order))
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
