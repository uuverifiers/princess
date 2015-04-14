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

package ap.proof;

import ap._
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.Predicate
import ap.terfor.equations.EquationConj
import ap.terfor.arithconj.{ModelElement, EqModelElement}
import ap.proof.goal._
import ap.util.{Logic, Debug, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._

import scala.collection.mutable.Stack

object ExhaustiveCCUProver {
  
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
           _ : AddFactsTask | _ : AllQuantifierTask => false
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
 * (Outdated description)
 *
 * A prover that tries to construct an exhaustive proof for a given goal. The
 * prover tries to optimise by early stopping the expansion of the proof tree
 * if it is detected that a certain subtree can never yield a satisfiable
 * closing constraint. There are two main modes of operation: with
 * <code>depthFirst</code>, it is tried to derive a satisfiable constraint from
 * the given problem, without aiming for exhaustiveness. Without this option,
 * the tree is expanded depth-first until it is exhaustive (which terminates
 * in the case of PA formulae, but not in general).
 */
class ExhaustiveCCUProver(depthFirst : Boolean, preSettings : GoalSettings) {

  def this(preSettings : GoalSettings) = this(false, preSettings)

  private val settings = {
    var gs = preSettings
    gs = Param.USE_WEAKEN_TREE.set(gs, false)
    gs = Param.FULL_SPLITTING.set(gs, true)
    gs = Param.CCU_SOLVER.set(gs,
           Param.CCU_STRATEGY(gs) match {
             case Param.CCUStrategyOptions.Table =>
               Some(new ccu.TableSolver(
                      () => Timeout.check,
                      Param.CLAUSIFIER_TIMEOUT(gs)))
             case Param.CCUStrategyOptions.Lazy =>
               Some(new ccu.LazySolver(
                      () => Timeout.check,
                      Param.CLAUSIFIER_TIMEOUT(gs)))
             case Param.CCUStrategyOptions.Bench =>
               Some(new ccu.BenchSolver(
                      () => Timeout.check,
                      Param.CLAUSIFIER_TIMEOUT(gs)))
           })
    gs
  }

  private val simplifier = Param.CONSTRAINT_SIMPLIFIER(settings)
  
  private def ptfStoppingCond(goal : Goal) = {
    Timeout.check
    assert(!goal.tasks.max.isInstanceOf[WrappedFormulaTask]) // should currently not happen
    ExhaustiveCCUProver ruleApplicationYield goal
  }

  private def addEliminatedEquations(t : ProofTree,
                                     eqs : EquationConj) : ProofTree = t match {
    case goal : Goal =>
      Goal(goal.facts, goal.compoundFormulas,
           goal.tasks, goal.age, goal.eliminatedConstants,
           goal.vocabulary, goal.definedSyms,
           goal.branchInferences,
           eqs :: goal.eliminatedEquations,
           goal.settings)
    case t : AndTree =>
      t.update(addEliminatedEquations(t.left, eqs),
               addEliminatedEquations(t.right, eqs),
               t.constantFreedom)
    case t : ProofTreeOneChild =>
      t.update(addEliminatedEquations(t.subtree, eqs), t.constantFreedom)
  }

  private val ptf = new IteratingProofTreeFactory(ptfStoppingCond _, simplifier) {
    override def eliminatedConstant(subtree : ProofTree,
                                    m : ModelElement,
                                    vocabulary : Vocabulary) : ProofTree =
      m match {
        case EqModelElement(eqs, _) =>
          addEliminatedEquations(subtree, eqs)
        case _ =>
          subtree
      }
  }
   
  //////////////////////////////////////////////////////////////////////////////

  def apply(inputFor : Formula, order : TermOrder) : ProofTree =
    apply(inputFor, Signature (Set(), inputFor.constants, Set(), order))

  def apply(inputFor : Formula, signature : Signature) : ProofTree = {
    val order = signature.order
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ExhaustiveCCUProver.AC,
                    inputFor.variables.isEmpty &&
                    (order isSortingOf inputFor) &&
                    Seqs.disjoint(inputFor.constants, signature.nullaryFunctions))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val goal = Goal(List(Conjunction.conj(inputFor, order)), Set(),
                    Vocabulary(order), settings)
    Timeout.unfinished {
      
      (if (depthFirst)
         expandDepthFirstUntilSat(goal, signature, 0)
//         expandDepthFirstUntilSatX(goal, false, signature, false) _1
       else
         expandFairUntilSat(goal, false, signature, false) _1)
        
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
    Debug.assertPre(ExhaustiveCCUProver.AC,
                    Seqs.disjoint(constraint.constants, signature.nullaryFunctions))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
//    throw new Exception

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
//    (tree.stepMeaningful || !tree.fixedConstantFreedom) &&
    // when proving in depth-first mode, a tree is expanded only as long as
    // its constraint is not satisfiable
    (!depthFirst || !tree.ccUnifiable
/*     (if (underConstraintWeakener)
        !(PresburgerTools isSatisfiable tree.closingConstraint)
      else
        !isValidConstraint(tree.closingConstraint, signature)) */
      )
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
    var swp : Boolean = swpBefore


    Console.err.println("====== Entering fair expansion")
    
    Timeout.unfinished {
      var cont : Boolean = !tree.ccUnifiable
      if (cont) {
        val expansionStack = new Stack[ExpansionStackItem]

        var goalCore : Set[Int] = tree.ccMinUnsolvableGoalSet.toSet
        if (goalCore.size != tree.goalCount)
          expansionStack push GoalCoreItem((0 until tree.goalCount).toSet)

        while (cont) {

  /*  println(tree)
     println(goalNum(tree))
     println  */

          Console.err.println("expanding goals " + (goalCore mkString " "))

          val (newTree, stepDone, oldEnd, newEnd, goalNumMapping) =
            expandProofGoalsSelectively(tree, goalCore, 0, 0)

          if (stepDone) {
            swp = true
            tree = newTree

            val newGoalCore =
              (for ((a, b) <- goalNumMapping.iterator; if (goalCore contains b))
               yield a).toSet

            val (unifiable, newMinCore) = tree.goalsAreCCUnifiable(newGoalCore)
            if (unifiable) {

              // search in the stack for the next group of goals to be
              // expanded
              var cumGoalNumMapping = goalNumMapping
              var cont2 = true

              while (cont2) {
                if (expansionStack.isEmpty) {
                  // then the whole subtree must be closable
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(ExhaustiveCCUProver.AC, tree.ccUnifiable)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  cont = false
                  cont2 = false
                } else expansionStack.pop match {
                  case GoalMappingItem(mapping) =>
                    cumGoalNumMapping = cumGoalNumMapping mapValues mapping
                  case GoalCoreItem(core) => {
                    val coreCandidate = (for ((a, b) <- cumGoalNumMapping.iterator;
                                              if (core contains b))
                                         yield a).toSet
                    val (unifiable, newMinCore) =
                      tree.goalsAreCCUnifiable(coreCandidate)
                    if (!unifiable) {
                      cont2 = false
                      expansionStack push GoalMappingItem(cumGoalNumMapping)

                      goalCore = newMinCore().toSet
                      if (goalCore != coreCandidate)
                        expansionStack push GoalCoreItem(coreCandidate)
                    }
                  }
                }
              }

            } else {
              if (newGoalCore != goalCore) {
                expansionStack push GoalMappingItem(goalNumMapping)
                goalCore = newMinCore().toSet

                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                Debug.assertInt(ExhaustiveCCUProver.AC,
                                !tree.goalsAreCCUnifiable(goalCore)._1)
                //-END-ASSERTION-///////////////////////////////////////////////

                if (goalCore.size != newGoalCore.size)
                  expansionStack push GoalCoreItem(newGoalCore)
              }
            }

          } else {
            cont = false
          }

          Timeout.check
        }
      }
  
    } {
      // if a timeout occurs, we return the proof tree that has been constructed
      // up to this point
      case _ => tree
    }
    
    Console.err.println("====== Leaving fair expansion")

    (tree, swp)
  }

  private sealed abstract class ExpansionStackItem
  private case class GoalCoreItem(goalCore : Set[Int])
               extends ExpansionStackItem
  private case class GoalMappingItem(mapping : Map[Int, Int])
               extends ExpansionStackItem

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Expand the proof depth-first until the root constraint is satisfiable
   * (or until <code>stoppingCond</code> returns <code>true</code>).
   */
  private def expandDepthFirstUntilSat(tree : ProofTree,
                                       signature : Signature,
                                       depth : Int)
                                      : ProofTree = {
    Timeout.unfinishedValue(tree) { Timeout.check }

    tree match {

      case PrefixedTree(_, _ : Goal) =>
        if (tree.ccUnifiable) {
          // we are finished here
          tree
        } else {
          (Timeout.unfinishedValue(tree) {
            Console.err.println("applying rule ...")
            expandProofGoals(tree)
           }) match {

            case (newTree, true) =>
              expandDepthFirstUntilSat(newTree, signature, depth)

            case (_, false) =>
              // this problem is hopeless: we have a subtree to
              // which no further rules can be applied, and
              // that cannot be closed
              tree

          }
        }

      case PrefixedTree(prefix, subtree : AndTree) => {

        val newLeft =
          Timeout.unfinished {
            Console.err.println("depth " + (depth + 1))
            expandDepthFirstUntilSat(subtree.left, signature, depth + 1)
          } {
            case lastTree : ProofTree =>
              prefix(subtree.update(lastTree, subtree.right,
                                    ConstantFreedom.BOTTOM))
          }

        if (newLeft.ccUnifiable) {
          val newRight =
            Timeout.unfinished {
            Console.err.println("depth " + (depth + 1))
              expandDepthFirstUntilSat(subtree.right, signature, depth + 1)
            } {
              case lastTree : ProofTree =>
                prefix(subtree.update(newLeft, lastTree,
                                      ConstantFreedom.BOTTOM))
            }
        
          val newTree =
            prefix(subtree.update(newLeft, newRight, ConstantFreedom.BOTTOM))

          if (newRight.ccUnifiable)
            expandFairUntilSat(newTree, false, signature, true)._1
          else
            newTree
        } else {
          prefix(subtree.update(newLeft, subtree.right, ConstantFreedom.BOTTOM))
        }

      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object PrefixedTree {
    def unapply(t : ProofTree) : Option[(ProofTree => ProofTree, ProofTree)] = {
      var subtree : ProofTree = t
      while (subtree.isInstanceOf[QuantifiedTree])
        subtree = subtree.asInstanceOf[QuantifiedTree].subtree

      Some((
        newSubtree => {
          def update(s : ProofTree) : ProofTree = s match {
            case s : QuantifiedTree =>
              s.update(update(s.subtree), s.constantFreedom)
            case _ =>
              newSubtree
          }
          update(t)
        },
        subtree
      ))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Try to expand each goal of <code>tree</code> by applying <code>limit</code>
   * steps. The result is a pair consisting of the new proof tree and a boolean
   * that tells whether it was possible to apply any steps
   */
  private def expandProofGoals(tree : ProofTree) : (ProofTree, Boolean) =
    if ((//tree.stepMeaningful && 
         (!depthFirst || !tree.ccUnifiableLocally)))
      tree match {
      
      case PrefixedTree(prefix, goal : Goal) => {
        val freedomFixed = goal.ccuFixedConstantFreedom
        if (goal.stepPossible || !freedomFixed) {
          val newGoal =
            if (freedomFixed)
              goal
            else
              goal updateConstantFreedom goal.ccuClosingConstantFreedom
          (prefix(newGoal.step(ptf)), true)
        } else {
          (tree, false)
        }
      }

      case PrefixedTree(prefix, tree : AndTree) => {
        val (newLeft, leftSWP) = expandProofGoals(tree.left)
        val (newRight, rightSWP) = expandProofGoals(tree.right)
        (prefix(tree.update(newLeft, newRight, tree.constantFreedom)),
         leftSWP || rightSWP)
      }
      
    } else {
      (tree, false)
    }

  //////////////////////////////////////////////////////////////////////////////
   
  private def expandProofGoalsSelectively
                 (tree : ProofTree,
                  goals : Set[Int],
                  oldStartIndex : Int,
                  newStartIndex : Int)
                : (ProofTree, Boolean, Int, Int, Map[Int, Int]) =
    tree match {
      
      case PrefixedTree(prefix, goal : Goal) =>
        if ((goals contains oldStartIndex) &&
            (goal.stepPossible || !goal.ccuFixedConstantFreedom)) {
          val newGoal =
            if (goal.ccuFixedConstantFreedom)
              goal
            else
              goal updateConstantFreedom goal.ccuClosingConstantFreedom
          val newTree = prefix(newGoal.step(ptf))
          val goalIndexMap =
            (for (i <- 0 until newTree.goalCount)
             yield (newStartIndex + i, oldStartIndex)).toMap
          (newTree, true,
           oldStartIndex + 1, newStartIndex + newTree.goalCount, goalIndexMap)
        } else {
          (tree, false,
           oldStartIndex + 1, newStartIndex + 1,
           Map(newStartIndex -> oldStartIndex))
        }

      case PrefixedTree(prefix, tree : AndTree) => {
        val (newLeft, leftSWP, oldStartIndex2, newStartIndex2, mapLeft) =
          expandProofGoalsSelectively(tree.left, goals,
                                      oldStartIndex, newStartIndex)
        val (newRight, rightSWP, oldStartIndex3, newStartIndex3, mapRight) =
          expandProofGoalsSelectively(tree.right, goals,
                                      oldStartIndex2, newStartIndex2)
        (prefix(tree.update(newLeft, newRight, tree.constantFreedom)),
         leftSWP || rightSWP,
         oldStartIndex3, newStartIndex3, mapLeft ++ mapRight)
      }
    }
      
}
