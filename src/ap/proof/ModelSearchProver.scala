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
import ap.basetypes.IdealInt
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.arithconj.ArithConj
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.terfor.substitutions.{Substitution, IdentitySubst}
import ap.terfor.preds.PredConj
import ap.proof.goal.{Goal, NegLitClauseTask, AddFactsTask, CompoundFormulas}
import ap.proof.certificates.{Certificate, CertFormula, PartialCertificate}
import ap.util.{Debug, Logic, LRUCache, FilterIt, Seqs, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._


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
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ModelSearchProver.AC,
                    inputFor.variables.isEmpty && (order isSortingOf inputFor))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    cache(inputFor) {
      applyHelp(List(Conjunction.conj(inputFor, order)),
                order, GoalSettings.DEFAULT,
                (_) => true).left.get
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
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ModelSearchProver.AC,
                    inputDisjuncts forall ((inputFor) =>
                      inputFor.variables.isEmpty && (order isSortingOf inputFor)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    applyHelp(inputDisjuncts, order,
              Param.CONSTRAINT_SIMPLIFIER.set(settings, simplifier),
              (_) => true)
  }
   
  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>None</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  private def applyHelp(disjuncts : Seq[Conjunction], order : TermOrder,
                        settings : GoalSettings,
                        modelSelector : Conjunction => Boolean)
                       : Either[Conjunction, Certificate] = {
    val elimConstants = order.orderedConstants
    val vocabulary =
      Vocabulary(order,
                 BindingContext.EMPTY.addAndContract(elimConstants, Quantifier.ALL),
                 ConstantFreedom.BOTTOM addTopStatus elimConstants)
    val goal = Goal(disjuncts, elimConstants, vocabulary, settings)

    //    val model = findModelFair(goal, 500)
    findModel(goal, List(), Set(), 0, settings, true, modelSelector) match {
      case SatResult =>
        Left(Conjunction.TRUE)
      case ModelResult(model) =>
        Left(model)
      case ModelResultCont(model) =>
        Left(model)
      case UnsatResult => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, !Param.PROOF_CONSTRUCTION(settings))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        Left(Conjunction.FALSE)
      }
      case UnsatCertResult(cert) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, Param.PROOF_CONSTRUCTION(settings))
        //-END-ASSERTION-///////////////////////////////////////////////////////

          /*
           * Some code to identify dangling formulae (assumed formulae that were
           * never provided) in a certificate
           * 
          val badFormula =
            (cert.assumedFormulas -- (Set() ++ (for (d <- disjuncts.iterator) yield d.negate))).iterator.next
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
          
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC,
                        cert.assumedFormulas subsetOf
                          (Set() ++ (for (d <- disjuncts.iterator)
                                       yield CertFormula(d.negate))))
        //-END-ASSERTION-///////////////////////////////////////////////////////
          
        Right(cert)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private sealed abstract class FindModelResult
  private case object SatResult                             extends FindModelResult
  private case class  ModelResult(model : Conjunction)      extends FindModelResult
  private case class  ModelResultCont(model : Conjunction)  extends FindModelResult
  private case object UnsatResult                           extends FindModelResult
  private case class  UnsatCertResult(cert : Certificate)   extends FindModelResult
  
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
                        settings : GoalSettings,
                        // construct a complete model?
                        constructModel : Boolean,
                        modelSelector : Conjunction => Boolean)
                       : FindModelResult = {
    Timeout.check
    
    tree match {
      case goal : Goal =>
        if (goal.facts.isFalse) {

//          println("backtracking " + depth)
          if (Param.PROOF_CONSTRUCTION(settings))
            UnsatCertResult(goal.getCertificate)
          else
            UnsatResult

        } else {

          // if the constant freedom of the goal has changed, we need to confirm
          // the update
          val uGoal =
            if ((!goal.stepPossible ||
                 (ExhaustiveProver ruleApplicationYield goal)) &&
                !goal.fixedConstantFreedom)
              goal updateConstantFreedom goal.closingConstantFreedom
            else
              goal
          
          if (uGoal.stepPossible)
            findModel(uGoal step ptf, witnesses, constsToIgnore, depth,
                      settings, constructModel, modelSelector)
          else
            handleSatGoal(uGoal, witnesses, constsToIgnore, depth,
                          settings, constructModel) match {
              case ModelResult(model) if (!modelSelector(model)) =>
                ModelResultCont(model)
              case r =>
                r
            }
          
        }
        
      case tree : WitnessTree =>
        findModel(tree.subtree, tree.witness :: witnesses, constsToIgnore,
                  depth, settings, constructModel, modelSelector)

      case tree : ProofTreeOneChild => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, tree match {
                          case _ : WeakenTree => false
                          case tree : QuantifiedTree => tree.quan == Quantifier.ALL
                          case _ => true
                        })
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val newConstsToIgnore = tree match {
          case tree : QuantifiedTree => constsToIgnore ++ tree.quantifiedConstants
          case _ => constsToIgnore
        }
        findModel(tree.subtree, witnesses, newConstsToIgnore, depth,
                  settings, constructModel, modelSelector)
      }
     
      case tree@AndTree(left, right, partialCert) => {
        // we use a local recursive function at this point to implement pruning 

        var pCert = partialCert

        def combineResults(leftTree : ProofTree,
                           rightTree : ProofTree) = handleAnds(leftTree) match {
          case UnsatResult => handleAnds(rightTree)
          case lr : ModelResultCont => handleAnds(rightTree) match {
            case r : ModelResult => r
            case r : ModelResultCont => r
            case _ => lr
          }
          case lr => lr
        }
        
        def handleAnds(tree : ProofTree) : FindModelResult = tree match {
          case tree@AndTree(left, right, null) =>
            combineResults(left, right)
          case tree =>
            findModel(tree, witnesses, constsToIgnore, depth + 1,
                      settings, constructModel, modelSelector) match {
              case UnsatCertResult(subCert) => (pCert bindFirst subCert) match {
                case Left(newPCert) => {
                  pCert = newPCert
                  UnsatResult
                }
                case Right(totalCert) => {
                  UnsatCertResult(totalCert)
                }
              }
              case r =>
                r
            }
        }
        
        combineResults(left, right) match {
          case UnsatResult => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
            Debug.assertInt(ModelSearchProver.AC, pCert == null)
            //-END-ASSERTION-///////////////////////////////////////////////////////
            UnsatResult
          }
          case r => r
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def assembleModel(arithModel : Conjunction,
                            literals : PredConj,
                            constsToIgnore : Set[ConstantTerm],
                            order : TermOrder) : Conjunction = {
    // assign constants not defined in the arithmetic model to zero
    val addEqs = EquationConj(for (c <- literals.constants -- arithModel.constants)
                                yield LinearCombination(c, order),
                              order)

    val modelWithPreds =
      Conjunction.conj(Array(arithModel, addEqs, literals), order)

    // quantify constants that we don't need
    val quantifiedModel = Conjunction.quantify(Quantifier.EX,
                                               order sort constsToIgnore,
                                               modelWithPreds, order)
    val simpModel = ReduceWithConjunction(Conjunction.TRUE, order)(quantifiedModel)
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ModelSearchProver.AC, !simpModel.isFalse)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    simpModel
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def handleSatGoal(goal : Goal,
                            // functions to reconstruct witnesses for eliminated
                            // constants
                            witnesses : List[(Substitution, TermOrder) => Substitution],
                            // explicitly quantified constants that do not have to
                            // be included in models
                            constsToIgnore : Set[ConstantTerm],
                            depth : Int,
                            settings : GoalSettings,
                            // construct a complete model?
                            constructModel : Boolean)
                           : FindModelResult = {
 
    // used in case we have to reset the constant freeness stored in the
    // goal

    def extractModel =
      if (!constructModel) {
        // we don't care about the precise model
        SatResult
      } else if (goal.constantFreedom.isBottom) {
        // we have indeed found a model
        
        val order = goal.order
        
        val constantValues : Substitution =
          (new IdentitySubst(order).asInstanceOf[Substitution] /: witnesses)(
                                                          (s, w) => w(s, order))
    
        val arithModel =
          EquationConj(for (c <- order.orderedConstants.iterator)
                       yield LinearCombination(Array((IdealInt.ONE, c),
                                                     (IdealInt.MINUS_ONE, constantValues(c))),
                                               order),
                       order)
        
        ModelResult(assembleModel(Conjunction.conj(arithModel, order),
                                  goal.facts.predConj, constsToIgnore, order))
      } else {
        // TODO: the proof generation could be switched off from this point on
        
    	val res = findModel(goal updateConstantFreedom ConstantFreedom.BOTTOM,
                            witnesses, constsToIgnore, depth,
                            settings, constructModel, (_) => true)

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        // We should be able to derive a counterexample
        Debug.assertPost(ModelSearchProver.AC, res match {
                           case ModelResult(model) => !model.isFalse
                           case ModelResultCont(model) => !model.isFalse
                           case _ => false
                         })
        //-END-ASSERTION-///////////////////////////////////////////////////////
        res
      }

    ////////////////////////////////////////////////////////////////////////////

    if (!goal.facts.arithConj.positiveEqs.isTrue &&
        !goal.constantFreedom.isBottomWRT(goal.facts.arithConj.positiveEqs.constants)) {

      // When constructing proofs, it can happen that not all
      // equations can be eliminated. We have to make sure that this
      // does not have any consequences for the created instantiations
      // of quantified formulae
    	
      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
      Debug.assertInt(ModelSearchProver.AC, Param.PROOF_CONSTRUCTION(settings))
      //-END-ASSERTION-///////////////////////////////////////////////////////

      val lowerConstantFreedom =
        goal.constantFreedom.findNonFreeness(
          Conjunction.conj(goal.facts.arithConj, goal.order).negate,
          goal.bindingContext)

      findModel(goal updateConstantFreedom lowerConstantFreedom,
   	            witnesses, constsToIgnore, depth, settings,
   	            constructModel, (m) => true)

    } else if (goal.facts.arithConj.isTrue) {
      
      // The goal is satisfiable, and we can extract a counterexample.
      // However, due to the free-constant optimisation, 
      // we might have to perform further splitting, etc. to construct a
      // genuine counterexample

      extractModel

    } else {

      // Not all arithmetic facts could be solved, which has to be because
      // of uninterpreted predicates or compound formulae
            
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelSearchProver.AC,
    		          (!goal.facts.predConj.isTrue || !goal.compoundFormulas.isEmpty))
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      // First continue proving only on the arithmetic facts

      val order = goal.order
      val newFacts = goal.facts.updatePredConj(PredConj.TRUE)(order)
      val newGoal =
    	nonRemovingPTF.updateGoal(Conjunction.TRUE, CompoundFormulas.EMPTY,
    			                  goal formulaTasks newFacts.negate, goal)

      findModel(newGoal, witnesses, Set(), depth, settings,
                constructModel, (_) => true) match {
        case SatResult =>
          SatResult
        
        case _ : ModelResult if (!constructModel) =>
          SatResult
        
        case ModelResult(model) if (goal.constantFreedom.isBottom) =>
          ModelResult(assembleModel(model, goal.facts.predConj,
                                    constsToIgnore, goal.order))

        case ModelResult(_) =>
          // The goal is satisfiable, and we can extract a counterexample.
          // However, due to the free-constant optimisation, 
          // we might have to perform further splitting, etc. to construct a
          // genuine counterexample

          extractModel

        case res => res
      }

    }
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
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
                      (goal.order isSubOrderOf newOrder) &&
                      goal.bindingContext.constantSeq.size <= 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
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
            case _ : NegLitClauseTask | _ : AddFactsTask => true
            case _ => false
          }
        if (cont)
          resGoal = (resGoal step ptf).asInstanceOf[Goal]
      }
      
      new IncProver(resGoal)
    }
    
    def checkValidity(constructModel : Boolean,
                      modelSelector : Conjunction => Boolean = (_) => true)
                     : Either[Conjunction, Certificate] =
      findModel(goal, List(), Set(), 0, goal.settings,
                constructModel, modelSelector) match {
        case SatResult             => Left(Conjunction.TRUE)
        case ModelResult(model)    => Left(model)
        case ModelResultCont(model)=> Left(model)
        case UnsatResult           => Left(Conjunction.FALSE)
        case UnsatCertResult(cert) => Right(cert)
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

/*                           
object TreeLogger {
  
  private var lines : List[String] = List()
  
  def += (l : String) : Unit = (lines = l :: lines)
  
  def enterScope[A](comp : => A) : A = {
    val currentLen = lines.size
    try { comp }
    finally {
      lines = lines drop (lines.size - currentLen)
    }
  }
  
  def print = for (s <- lines.reverse) println(s) 
  
}
*/                     
