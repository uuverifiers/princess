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

package ap.proof;

import ap._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier,
                               ReduceWithConjunction}
import ap.proof.goal._
import ap.util.{Logic, Debug, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._

object ExhaustiveProver {
  
  private def AC = Debug.AC_PROVER
  
  def ruleApplicationYield(goal : Goal) : Boolean = goal.tasks.max match {
 //   case FactsNormalisationTask | EliminateFactsTask |
 //        _ : AddFactsTask | _ : NegLitClauseTask => false
      case WrappedFormulaTask(_ : BetaFormulaTask, simpTasks) =>
        simpTasks exists {
          case _ : BetaFormulaTask |
               _ : ExQuantifierTask => true
          case _ => false
        } 
      case FactsNormalisationTask | EliminateFactsTask | UpdateTasksTask |
           _ : UpdateConstantFreedomTask | EagerMatchTask |
           _ : AddFactsTask => false
      case _ : LazyMatchTask =>
        // if there are no clauses, matching is trivial
        !goal.compoundFormulas.lazyQuantifiedClauses.clauses.isTrue
      case task : BetaFormulaTask => !task.addToQFClauses
      case task : DivisibilityTask => task.splittingNecessary(goal)
      case OmegaTask => OmegaTask.splittingNecessary(goal)
      case _ => true
  }
  
}

/**
 * A prover that tries to construct an exhaustive proof for a given goal. The
 * prover tries to optimise by early stopping the expansion of the proof tree
 * if it is detected that a certain subtree can never yield a satisfiable
 * closing constraint. There are two main modes of operation: with
 * <code>depthFirst</code>, it is tried to derive a satisfiable constraint from
 * the given problem, without aiming for exhaustiveness. Without this option,
 * the tree is expanded depth-first until it is exhaustive (which terminates
 * in the case of PA formulae, but not in general).
 */
class ExhaustiveProver(depthFirst : Boolean, settings : GoalSettings) {

  def this(settings : GoalSettings) = this(false, settings)

  private val simplifier = Param.CONSTRAINT_SIMPLIFIER(settings)
  
  private def ptfStoppingCond(goal : Goal) = {
    Timeout.check
    assert(!goal.tasks.max.isInstanceOf[WrappedFormulaTask]) // should currently not happen
    ExhaustiveProver ruleApplicationYield goal
  }

  private val ptf = new IteratingProofTreeFactory(ptfStoppingCond _, simplifier)
   
  //////////////////////////////////////////////////////////////////////////////

  def apply(inputFor : Conjunction, order : TermOrder) : ProofTree =
    apply(inputFor, new Signature (Set(), inputFor.constants, Set(), order))

  def apply(inputFor : Conjunction, signature : Signature) : ProofTree = {
    val order = signature.order
if (!(ReduceWithConjunction(Conjunction.TRUE, order)(inputFor) eq inputFor))
println(inputFor)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ExhaustiveProver.AC,
                    inputFor.variables.isEmpty &&
                    (order isSortingOf inputFor) &&
                    Seqs.disjoint(inputFor.constants, signature.nullaryFunctions) &&
                    // we assume that the input problem has already been simplified
                    (ReduceWithConjunction(Conjunction.TRUE, order)(inputFor) eq inputFor))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val goal = Goal(List(Conjunction.conj(inputFor, order)), Set(),
                    Vocabulary(order), settings)
    Timeout.unfinished {
      
      (if (depthFirst)
         expandDepthFirstUntilSat(goal, false, signature, false)
       else
         expandFairUntilSat(goal, false, signature, false)) _1
        
    } {
      case None => goal
      case x => x
    }
  }

  /**
   * A constraint is considered valid if the formula
   * <code>\forall universalConstants; \exists existentialConstants; constraint</code>
   * is valid
   */
  def isValidConstraint(constraint : Conjunction, signature : Signature) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ExhaustiveProver.AC,
                    Seqs.disjoint(constraint.constants, signature.nullaryFunctions))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (Seqs.disjoint(constraint.constants, signature.existentialConstants)) {
      PresburgerTools isValid constraint
    } else if (Seqs.disjoint(constraint.constants, signature.universalConstants)) {
      PresburgerTools isSatisfiable constraint
    } else {
      val order = constraint.order
      val quantifiedConstraint =
        Conjunction.quantify(Quantifier.EX,
                             order sort signature.existentialConstants,
                             constraint, order)
      PresburgerTools isValid simplifier(quantifiedConstraint, order)
    }
  }
  
  /**
   * Determine whether we should continue applying rules to the given (sub)tree.
   * The argument
   * <code>underConstraintWeakener</code> tells whether <code>tree</code> is
   * underneath a <code>QuantifiedTree</code> or <code>WeakenTree</code> node.
   */
  private def continueProving(tree : ProofTree, underConstraintWeakener : Boolean,
                              signature : Signature) = {
    Timeout.check
    (tree.stepMeaningful || !tree.fixedConstantFreedom) &&
    // when proving in depth-first mode, a tree is expanded only as long as
    // its constraint is not satisfiable
    (!depthFirst ||
     (if (underConstraintWeakener)
        !(PresburgerTools isSatisfiable tree.closingConstraint)
      else
        !isValidConstraint(tree.closingConstraint, signature)))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Expand the proof breadth-first until the root constraint is satisfiable
   * (or until <code>stoppingCond</code> returns <code>true</code>).
   * The result is a pair consisting of the new proof tree and a boolean
   * that tells whether it was possible to apply any steps. The argument
   * <code>underConstraintWeakener</code> tells whether <code>tree</code> is
   * underneath a <code>QuantifiedTree</code> or <code>WeakenTree</code> node.
   */
  private def expandFairUntilSat(_tree : ProofTree,
                                 underConstraintWeakener : Boolean,
                                 signature : Signature,
                                 swpBefore : Boolean) : (ProofTree, Boolean) = {
    var tree : ProofTree = _tree
    var cont : Boolean = true
    var swp : Boolean = swpBefore
    
    Timeout.unfinished {
      // if a timeout occurs, we return the proof tree that has been constructed
      // up to this point
      
      while (cont && continueProving(tree, underConstraintWeakener, signature)) {
  /*  println(tree)
     println(goalNum(tree))
     println  */
        val (newTree, newCont) =
          expandProofGoals(tree, tree.closingConstantFreedom, 1)
        tree = newTree
        cont = newCont
        if (newCont) swp = true
      }
      
    } {
      case _ => tree
    }
    
    (tree, swp)
  }

  private def isGoalLike(tree : ProofTree) : Boolean = tree match {
    case _ : Goal                                   => true
    case QuantifiedTree(Quantifier.ALL, _, subtree) => isGoalLike(subtree)
    case _                                          => false
  }

  /**
   * Expand the proof depth-first until the root constraint is satisfiable
   * (or until <code>stoppingCond</code> returns <code>true</code>).
   * The result is a pair consisting of the new proof tree and a boolean
   * that tells whether it was possible to apply any steps. The argument
   * <code>underConstraintWeakener</code> tells whether <code>tree</code> is
   * underneath a <code>QuantifiedTree</code> or <code>WeakenTree</code> node.
   */
  private def expandDepthFirstUntilSat(tree : ProofTree,
                                       underConstraintWeakener : Boolean,
                                       signature : Signature,
                                       swpBefore : Boolean)
                                                       : (ProofTree, Boolean) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // if there are free constants, we have to expand in a fair manner
    Debug.assertPre(ExhaustiveProver.AC, tree.constantFreedom.isBottom)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (Timeout.unfinishedValue(tree) {
          continueProving(tree, underConstraintWeakener, signature)
        })
      tree match {
      case _ if (isGoalLike(tree) ||
                 tree.subtrees.exists((subtree) =>
                                      !subtree.constantFreedom.isBottom)) => {
        // we always consider the goal together with the enclosing universal
        // quantifiers
        val (newTree, swp) =
          Timeout.unfinishedValue(tree) {
            expandProofGoals(tree, ConstantFreedom.BOTTOM, 1)
          }
        
        if (swp) {
          // recurse because the structure of the tree might have changed
          expandDepthFirstUntilSat(newTree, underConstraintWeakener, signature, true)
        } else {
          // we continue in a fair manner
          expandFairUntilSat(newTree, underConstraintWeakener, signature, swpBefore)
        }
      }
      
      case goal : Goal => {
        val goalOneStep = Timeout.unfinishedValue(goal) { goal step ptf }
        expandDepthFirstUntilSat(goalOneStep, underConstraintWeakener, signature, true)
      }
      
      case tree : ProofTreeOneChild => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ExhaustiveProver.AC,
                        tree.isInstanceOf[QuantifiedTree] ||
                        tree.isInstanceOf[WeakenTree])
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val (newSubtree, swp) =
          Timeout.unfinished {
            expandDepthFirstUntilSat(tree.subtree, true, signature, false)
          } {
            case lastTree : ProofTree =>
              tree.update(lastTree, ConstantFreedom.BOTTOM)
          }
        val newTree = tree.update(newSubtree, ConstantFreedom.BOTTOM)
        
        if (swp) {
          // recurse because the structure of the tree might have changed
          expandDepthFirstUntilSat(newTree, underConstraintWeakener, signature, true)
        } else {
          // we continue in a fair manner
          expandFairUntilSat(newTree, underConstraintWeakener, signature, swpBefore)
        }        
      }
      
      case tree : AndTree => {
        val (newLeft, leftSWP) =
          Timeout.unfinished {
            expandDepthFirstUntilSat(tree.left, underConstraintWeakener, signature, false)
          } {
            case lastTree : ProofTree =>
              tree.update(lastTree, tree.right, ConstantFreedom.BOTTOM)
          }
        val (newRight, rightSWP) =
          Timeout.unfinished {
            expandDepthFirstUntilSat(tree.right, underConstraintWeakener, signature, false)
          } {
            case lastTree : ProofTree =>
              tree.update(newLeft, lastTree, ConstantFreedom.BOTTOM)
          }
        
        val newTree = tree.update(newLeft, newRight, ConstantFreedom.BOTTOM)
        
        if (leftSWP || rightSWP) {
          // recurse because the structure of the tree might have changed
          expandDepthFirstUntilSat(newTree, underConstraintWeakener, signature, true)
        } else {
          // we continue in a fair manner
          expandFairUntilSat(newTree, underConstraintWeakener, signature, swpBefore)
        }
      }
    } else {
      // otherwise, the tree is already satisfiable (or at least the constraint
      // is not false .. TODO) or no more steps are possible
      (tree, swpBefore)
    }
  }
  
  /**
   * Try to expand each goal of <code>tree</code> by applying <code>limit</code>
   * steps. The result is a pair consisting of the new proof tree and a boolean
   * that tells whether it was possible to apply any steps
   */
  private def expandProofGoals(tree : ProofTree,
                               newConstantFreedom : ConstantFreedom,
                               limit : Int) : (ProofTree, Boolean) =
    if (limit > 0 &&
        (tree.stepMeaningful && (!depthFirst || !tree.closingConstraint.isTrue)
         ||
         newConstantFreedom != tree.constantFreedom || !tree.fixedConstantFreedom))
      tree match {
      
      case goal : Goal => {
        val updatedGoal = goal updateConstantFreedom newConstantFreedom
        val newTree =
          if (updatedGoal.stepPossible)
            expandProofGoals(updatedGoal.step(ptf), newConstantFreedom, limit - 1) _1
          else
            updatedGoal
        (newTree, true)  // also updating the set of free constants is
                         // considered as a proof step
      }
      
      case tree : ProofTreeOneChild => {
        val (newSubtree, stepWasPossible) =
          expandProofGoals(tree.subtree,
                           tree newConstantFreedomForSubtree newConstantFreedom,
                           limit)
        (tree.update(newSubtree, newConstantFreedom), stepWasPossible)
      }
      
      case tree : AndTree => {
        val (leftCF, rightCF) = tree newConstantFreedomForSubtrees newConstantFreedom
        val (newLeft, leftSWP) = expandProofGoals(tree.left, leftCF, limit)
        val (newRight, rightSWP) = expandProofGoals(tree.right, rightCF, limit)        
        (tree.update(newLeft, newRight, newConstantFreedom), leftSWP || rightSWP)
      }
      
    } else {
      (tree, false)
    }
   
   private def goalNum(tree : ProofTree) : Int = tree match {
     case g : Goal => if (g.closingConstraint.isTrue) 0 else 1
     case t : ProofTreeOneChild => goalNum(t.subtree)
     case t : AndTree => goalNum(t.left) + goalNum(t.right)
   }
}
