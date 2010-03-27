/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof;

import ap.basetypes.IdealInt
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.terfor.substitutions.{Substitution, IdentitySubst}
import ap.proof.goal.{Goal, NegLitClauseTask}
import ap.proof.certificates.Certificate
import ap.util.{Debug, Logic, LRUCache, FilterIt, Seqs}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._

import scala.collection.mutable.Stack


/**
 * A prover that tries to construct a countermodel of a ground formula. This
 * prover works in depth-first mode, in contrast to the
 * <code>ExhaustiveProver</code>.
 */
object ModelSearchProver {

  private val AC = Debug.AC_PROVER
   
  private val simplifier = ConstraintSimplifier.FAIR_SIMPLIFIER
  
  // we need to store eliminated facts from goals, otherwise we could not
  // construct a complete model
  private val ptf = new SimpleProofTreeFactory(true, simplifier) {
    override def eliminatedConstant(subtree : ProofTree,
                                    c : ConstantTerm,
                                    witness : (Substitution, TermOrder) => Substitution,
                                    vocabulary : Vocabulary) : ProofTree =
      new WitnessTree (subtree, c, witness, vocabulary)
  }

  private val nonRemovingPTF = new SimpleProofTreeFactory(false, simplifier)
  
  private val cache = new LRUCache[Formula, Conjunction] (1000)
  
  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>FALSE</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  def apply(inputFor : Formula, order : TermOrder) : Conjunction = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(ModelSearchProver.AC,
                    inputFor.variables.isEmpty && (order isSortingOf inputFor))
    ////////////////////////////////////////////////////////////////////////////
    cache(inputFor) {
      applyHelp(List(Conjunction.conj(inputFor, order)),
                order, GoalSettings.DEFAULT).left.get
    }
  }

  /**
   * <code>inputDisjuncts</code> are the formulae (connected disjunctively) to
   * be disproven. The result of the method is either countermodel of
   * <code>inputDisjuncts</code> (the case <code>Left</code>), or a proof of
   * validity (<code>Right</code>). In case proof construction is disabled,
   * the validity result will be <code>Left(FALSE)</code>.
   */
  def apply(inputDisjuncts : Seq[Conjunction], order : TermOrder,
            settings : GoalSettings) : Either[Conjunction, Certificate] = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(ModelSearchProver.AC,
                    inputDisjuncts forall ((inputFor) =>
                      inputFor.variables.isEmpty && (order isSortingOf inputFor)))
    ////////////////////////////////////////////////////////////////////////////
    applyHelp(inputDisjuncts, order,
              Param.CONSTRAINT_SIMPLIFIER.set(settings, simplifier))
  }
   
  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>None</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  private def applyHelp(inputDisjuncts : Seq[Conjunction], order : TermOrder,
                        settings : GoalSettings) : Either[Conjunction, Certificate] = {
    val disjuncts = if (Param.PROOF_CONSTRUCTION(settings)) {
      inputDisjuncts
    } else {
      val reducer = ReduceWithConjunction(Conjunction.TRUE, order)
      for (d <- inputDisjuncts) yield reducer(d)
    }
    val elimConstants = order.orderedConstants
    val vocabulary =
      Vocabulary(order,
                 BindingContext.EMPTY.addAndContract(elimConstants, Quantifier.ALL),
                 ConstantFreedom.BOTTOM addTopStatus elimConstants)
    val goal = Goal(disjuncts, elimConstants, vocabulary, settings)

    //    val model = findModelFair(goal, 500)
    findModel(goal, List(), Set(), 0, settings) match {
      case Left(model) =>
        Left(model)
      case Right(certificates) => {
        if (Param.PROOF_CONSTRUCTION(settings)) {
          //////////////////////////////////////////////////////////////////////
          Debug.assertInt(ModelSearchProver.AC,
                          certificates.size == 1 && certificates(0) != null)
          //////////////////////////////////////////////////////////////////////
          val Seq(cert) = certificates

          /*
           * Some code to identify dangling formulae (assumed formulae that were
           * never provided) in a certificate
           * 
          val badFormula =
            (cert.assumedFormulas -- (Set() ++ (for (d <- disjuncts.elements) yield d.negate))).elements.next
          println(badFormula)

          def traceBF(c : Certificate) : Unit = {
            println(c)
            for (d <- c) {
              if (d.assumedFormulas contains badFormula)
                traceBF(d)
            }
          }
          
          traceBF(cert)
          */
          
          //////////////////////////////////////////////////////////////////////
          Debug.assertInt(ModelSearchProver.AC,
                          cert.assumedFormulas subsetOf
                            (Set() ++ (for (d <- disjuncts.elements) yield d.negate)))
          //////////////////////////////////////////////////////////////////////
          
          Right(cert)
        } else {
          Left(Conjunction.FALSE)
        }
      }
    }
  }

  private def isSatisfiableGoal(tree : ProofTree) : Boolean = tree match {
    case goal : Goal => PresburgerTools.isValid(goal.closingConstraint)
    case _ => false
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Construct either a countermodel or a proof for a conjecture. In case no
   * the current settings are to not produce proofs, only
   * <code>Right(List())</code> is returned for the proof case.
   */
  private def findModel(tree : ProofTree,
                        // functions to reconstruct witnesses for eliminated
                        // constants
                        witnesses : List[(Substitution, TermOrder) => Substitution],
                        // explicitly quantified constants that do not have to
                        // be included in models
                        constsToIgnore : Set[ConstantTerm],
                        depth : Int,
                        settings : GoalSettings) : Either[Conjunction, Seq[Certificate]] = {
    Timeout.check
    
    tree match {
      case goal : Goal =>
        if (goal.facts.isFalse) {
//          println("backtracking " + depth)
          Right(if (Param.PROOF_CONSTRUCTION(settings))
                  List(goal.getCertificate)
                else
                  List())
        } else {
          // if the constant freedom of the goal has changed, we need to confirm
          // the update
          val uGoal =
            if (!goal.fixedConstantFreedom &&
                (!goal.stepPossible ||
                 (ExhaustiveProver ruleApplicationYield goal)))
              goal updateConstantFreedom goal.closingConstantFreedom
            else
              goal
          
          if (uGoal.stepPossible)
            findModel(uGoal step ptf, witnesses, constsToIgnore, depth, settings)
          else if (isSatisfiableGoal(uGoal))
            Right(if (Param.PROOF_CONSTRUCTION(settings))
                    List(uGoal.getCertificate)
                  else
                    List())
          else if (uGoal.compoundFormulas.qfClauses.isTrue)
            Left(constructModel(uGoal.facts,
                                witnesses, constsToIgnore,
                                uGoal.order))
          else {
            // the free constant optimisation can lead to the situation that
            // not all formulae are fully split; in this case, we have to
            // continue proving to derive a full counterexample
            
            val order = uGoal.order
            val disjuncts =
              List(uGoal.facts.negate) ++ uGoal.compoundFormulas.qfClauses
            val newGoal = Goal(disjuncts, uGoal.eliminatedConstants,
                               Vocabulary(order), uGoal.settings)
              
            findModel(newGoal, witnesses, constsToIgnore, depth, settings)
          }
        }
        
      case tree : WitnessTree =>
        findModel(tree.subtree, tree.witness :: witnesses, constsToIgnore,
                  depth, settings)

      case tree : ProofTreeOneChild => {
        ////////////////////////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, tree match {
                          case _ : WeakenTree => false
                          case tree : QuantifiedTree => tree.quan == Quantifier.ALL
                          case _ => true
                        })
        ////////////////////////////////////////////////////////////////////////
        val newConstsToIgnore = tree match {
          case tree : QuantifiedTree => constsToIgnore ++ tree.quantifiedConstants
          case _ => constsToIgnore
        }
        findModel(tree.subtree, witnesses, newConstsToIgnore, depth, settings)
      }
     
      case AndTree(left, right, partialCert) => {
        findModel(left, witnesses, constsToIgnore, depth + 1, settings) match {
          case res @ Left(_) =>
            res
          case Right(leftCerts) =>
            findModel(right, witnesses, constsToIgnore, depth + 1, settings) match {
              case res @ Left(_) =>
                res
              case Right(rightCerts) =>
                Right(if (leftCerts.isEmpty || rightCerts.isEmpty)
                        List()
                      else if (partialCert == null)
                        leftCerts ++ rightCerts
                      else
                        List(partialCert(leftCerts ++ rightCerts)))
            }
        }
      }
    }
  }

  private def constructModel(facts : Conjunction,
                             witnesses : List[(Substitution, TermOrder) => Substitution],
                             constsToIgnore : Set[ConstantTerm],
                             order : TermOrder) : Conjunction = {
    val constantValues : Substitution =
      (new IdentitySubst(order).asInstanceOf[Substitution] /: witnesses)(
                                                         (s, w) => w(s, order))
    
    val valuesConj =
      EquationConj(for (c <- (order.orderedConstants -- constsToIgnore).elements)
                   yield LinearCombination(Array((IdealInt.ONE, c),
                                                 (IdealInt.MINUS_ONE, constantValues(c))),
                                           order),
                   order)
    Conjunction.conj(Array(valuesConj, facts), order)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Prover that can be used incrementally
  
  def emptyIncProver(settings : GoalSettings) : IncProver =
    new IncProver(Goal(List(), Set(), Vocabulary(TermOrder.EMPTY), settings))
  
  class IncProver protected[proof] (goal : Goal) {
    
    def assert(f : Conjunction, newOrder : TermOrder) : IncProver =
      conclude(f.negate, newOrder)

    def assert(fors : Iterable[Conjunction],
               newOrder : TermOrder) : IncProver =
      conclude(for (f <- fors) yield f.negate, newOrder)

    def conclude(f : Conjunction, newOrder : TermOrder) : IncProver =
      conclude(List(f), newOrder)

    def conclude(fors : Iterable[Conjunction],
                 newOrder : TermOrder) : IncProver = {
      //////////////////////////////////////////////////////////////////////////
      Debug.assertPre(AC,
                      (goal.order isSubOrderOf newOrder) &&
                      goal.bindingContext.constantSeq.size <= 1)
      //////////////////////////////////////////////////////////////////////////
      
      // check whether we have to update the <code>TermOrder</code> of the goal
      val newOrderGoal =
        if (newOrder == goal.order) {
          goal
        } else {
          val newConsts = newOrder.orderedConstants -- goal.order.orderedConstants
          val newVocabulary =
            Vocabulary(newOrder,
                       goal.bindingContext.addAndContract(newConsts, Quantifier.ALL),
                       goal.constantFreedom addTopStatus newConsts)

          nonRemovingPTF.updateGoal(goal.eliminatedConstants ++ newConsts,
                                    newVocabulary, List(),
                                    goal).asInstanceOf[Goal]
        }
      
      var resGoal = newOrderGoal addTasksFor fors
      
      // apply the most simple tasks right away
      var cont = true
      while (cont && resGoal.stepPossible) {
        cont = resGoal.tasks.max match {
            case _ : NegLitClauseTask => true
            case _ => false
          }
        if (cont)
          resGoal = (resGoal step ptf).asInstanceOf[Goal]
      }
      
      new IncProver(resGoal)
    }
    
    def checkValidity : Either[Conjunction, Certificate] =
      findModel(goal, List(), Set(), 0, goal.settings) match {
        case Left(model) => Left(model)
        case Right(Seq()) => Left(Conjunction.FALSE)
        case Right(Seq(cert)) => Right(cert)
      }
    
  }
  
}

 
private case class WitnessTree(val subtree : ProofTree,
                               val eliminatedConstant : ConstantTerm,
                               val witness : (Substitution, TermOrder) => Substitution,
                               val vocabulary : Vocabulary)
                   extends { protected val subtreeOrder = vocabulary.order }
                           with ProofTreeOneChild {

  def update(newSubtree : ProofTree, newConstantFreedom : ConstantFreedom) : ProofTree =
    new WitnessTree(subtree, eliminatedConstant, witness,
                    vocabulary updateConstantFreedom newConstantFreedom)

  lazy val closingConstraint : Conjunction =
    subtree.closingConstraint

  lazy val closingConstantFreedom : ConstantFreedom =
    subtree.closingConstantFreedom

  lazy val fixedConstantFreedom : Boolean =
    subtree.fixedConstantFreedom

  lazy val stepMeaningful : Boolean =
    subtree.stepMeaningful
  
  def newConstantFreedomForSubtree(cf : ConstantFreedom) : ConstantFreedom = cf
}