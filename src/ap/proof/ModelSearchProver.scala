/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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
import ap.basetypes.IdealInt
import ap.terfor.{Formula, TermOrder, ConstantTerm}
import ap.terfor.arithconj.{ArithConj, ModelElement}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.terfor.substitutions.{Substitution, IdentitySubst}
import ap.terfor.preds.PredConj
import ap.proof.goal.{Goal, NegLitClauseTask, AddFactsTask, CompoundFormulas,
                      TaskManager, PrioritisedTask}
import ap.proof.certificates.{Certificate, CertFormula, PartialCertificate}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._
import ap.util.{Debug, Logic, LRUCache, FilterIt, Seqs, Timeout}

import scala.collection.mutable.ArrayBuilder

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
                                    m : ModelElement,
                                    vocabulary : Vocabulary) : ProofTree =
      new WitnessTree (subtree, m, vocabulary)
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
    cache.cached(inputFor) {
      applyHelp(List(Conjunction.conj(inputFor, order)),
                order, GoalSettings.DEFAULT, FullModelDirector).left.get
    } {
      result => result sortBy order
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
              FullModelDirector)
  }
   
  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>None</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  private def applyHelp(disjuncts : Seq[Conjunction], order : TermOrder,
                        rawSettings : GoalSettings,
                        searchDirector : (Conjunction, Boolean) => SearchDirection)
                       : Either[Conjunction, Certificate] = {
    val settings = Param.APPLY_BLOCKED_TASKS.set(rawSettings, true)
    val elimConstants = order.orderedConstants
    val vocabulary =
      Vocabulary(order,
                 BindingContext.EMPTY.addAndContract(elimConstants, Quantifier.ALL),
                 ConstantFreedom.BOTTOM addTopStatus elimConstants)
    val goal = Goal(disjuncts, elimConstants, vocabulary, settings)

    //    val model = findModelFair(goal, 500)
    findModel(goal, List(), List(), Set(), 0, settings, searchDirector) match {
      case SatResult =>
        Left(Conjunction.TRUE)
      case ModelResult(model) =>
        Left(model)
      case UnsatResult | UnsatEFResult(_) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, !Param.PROOF_CONSTRUCTION(settings))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        Left(Conjunction.FALSE)
      }
      case EFRerunResult(_) =>
        // this should never happen
        throw new IllegalArgumentException
      case UnsatCertResult(cert) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, Param.PROOF_CONSTRUCTION(settings))
        //-END-ASSERTION-///////////////////////////////////////////////////////

          /*
           * Some code to identify dangling formulae (assumed formulae that were
           * never provided) in a certificate
           * 
          val badFormula =
            (cert.assumedFormulas --
             (Set() ++ (for (d <- disjuncts.iterator) yield CertFormula(d.negate)))).iterator.next
          println(badFormula)

          def traceBF(c : Certificate) : Unit = {
            println(c)
            for (d <- c.subCertificates) {
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
  private case object SatResult                         extends FindModelResult
  private case object UnsatResult                       extends FindModelResult
  private case class  UnsatEFResult(extraFFors : Seq[Conjunction])
                                                        extends FindModelResult
  private case class  EFRerunResult(extraFFors : Seq[Conjunction])
                                                        extends FindModelResult
  private case class  UnsatCertResult(cert : Certificate)
                                                        extends FindModelResult
  private case class  ModelResult(model : Conjunction)  extends FindModelResult
  
  //////////////////////////////////////////////////////////////////////////////

  sealed abstract class SearchDirection
  case object ReturnSatDir                              extends SearchDirection
  case object AcceptModelDir                            extends SearchDirection
  case object DeriveFullModelDir                        extends SearchDirection
  case object NextModelDir                              extends SearchDirection
  case class  AddFormulaDir(formula : Conjunction)      extends SearchDirection
  
  private val FullModelDirector : (Conjunction, Boolean) => SearchDirection = {
    case (_, false) => DeriveFullModelDir
    case (_, true) => AcceptModelDir
  }
  
  private val SatOnlyDirector : (Conjunction, Boolean) => SearchDirection = {
    case _ => ReturnSatDir
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Construct either a countermodel or a proof for a conjecture. In case no
   * the current settings are to not produce proofs, only
   * <code>Right(List())</code> is returned for the proof case.
   */
  private def findModel(tree : ProofTree,
                        // formula to be added to the goals of the tree
                        extraFormulae : Seq[Conjunction],
                        // functions to reconstruct witnesses for eliminated
                        // constants
                        witnesses : List[ModelElement],
                        // explicitly quantified constants that do not have to
                        // be included in models
                        constsToIgnore : Set[ConstantTerm],
                        depth : Int,
                        settings : GoalSettings,
                        // given a model, and a flag telling whether the model
                        // is partial (only the facts of the current goal) or has
                        // been completed using all information available, decide
                        // how to continue search
                        searchDirector : (Conjunction, Boolean) => SearchDirection)
                       : FindModelResult = {
    Timeout.check
    
    tree match {
      case goal : Goal =>
        if (goal.facts.isFalse) {
          // we have to backtrack
          
//          println("backtracking " + depth)
          if (Param.PROOF_CONSTRUCTION(settings))
            UnsatCertResult(goal.getCertificate)
          else
            UnsatResult

        } else if (!extraFormulae.isEmpty) {
          // there are some further formulae to be added to be goal before
          // we continue with the proof
          
          findModel(goal addTasksFor (
                      for (f <- extraFormulae) yield (goal reduceWithFacts f)),
                    List(), witnesses,
                    constsToIgnore, depth, settings, searchDirector)
          
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
          
          val res =
            if (uGoal.stepPossible)
              findModel(uGoal step ptf, extraFormulae, witnesses,
                        constsToIgnore, depth, settings, searchDirector)
            else
              handleSatGoal(uGoal, witnesses, constsToIgnore, depth,
                            settings, searchDirector)
          
          res match {
            case EFRerunResult(formulas)
              if (!ModelElement.containAffectedSymbols(formulas, witnesses)) =>
              // we have to start over from this point
              findModel(uGoal, formulas, witnesses,
                        constsToIgnore, depth, settings, searchDirector) match {
                case UnsatResult =>         UnsatEFResult(formulas)
                case UnsatEFResult(fors) => UnsatEFResult(formulas ++ fors)
                case EFRerunResult(fors) => EFRerunResult(formulas ++ fors)
                case UnsatCertResult(_) =>  throw new IllegalArgumentException
                case r =>                   r
              }
            case r => r
          }
        }
        
      case tree : WitnessTree =>
        findModel(tree.subtree, extraFormulae,
                  tree.modelElement :: witnesses, constsToIgnore,
                  depth, settings, searchDirector)

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
        findModel(tree.subtree, extraFormulae, witnesses, newConstsToIgnore, depth,
                  settings, searchDirector)
      }

      case tree@AndTree(left, right, partialCert) if (partialCert != null) => {
        var nonCertResult : FindModelResult = null

        val subCertIt = new Iterator[() => Certificate] {
          var treeStack = List(left, right)

          private def extractNextChild : Unit = treeStack match {
            case AndTree(l, r, null) :: tail => {
              treeStack = l :: r :: tail
              extractNextChild
            }
            case _ => // nothing
          }

          def hasNext = !treeStack.isEmpty

          def next = {
            extractNextChild
            val child = treeStack.head
            treeStack = treeStack.tail

            () => {
              findModel(child, extraFormulae, witnesses, constsToIgnore,
                        depth + 1, settings, searchDirector) match {
              case UnsatCertResult(cert) => cert
//              case UnsatEFResult(fors)   => ef = ef ++ fors
              case UnsatEFResult(_)      => throw new IllegalArgumentException
              case EFRerunResult(_)      => throw new IllegalArgumentException
              case UnsatResult           => throw new IllegalArgumentException
              case r => {
                nonCertResult = r
                null
              }
            }
          }}
        }

        partialCert.dfExplore(subCertIt) match {
          case null =>
            nonCertResult
          case res =>
            UnsatCertResult(res)
        }
      }
     
      case tree@AndTree(left, right, partialCert) => {
        // we use a local recursive function at this point to implement pruning 

        var pCert = partialCert
        var ef = extraFormulae

        def combineResults(leftTree : ProofTree,
                           rightTree : ProofTree) = handleAnds(leftTree) match {
          case UnsatResult =>
            handleAnds(rightTree)
          case lr@UnsatEFResult(formulae) =>
            handleAnds(rightTree) match {
              case UnsatEFResult(formulae2) => UnsatEFResult(formulae ++ formulae2)
              case EFRerunResult(formulae2) => EFRerunResult(formulae ++ formulae2)
              case UnsatResult => lr
              case r => r
            }
          case lr => lr
        }
        
        def handleAnds(tree : ProofTree) : FindModelResult = tree match {
          case tree@AndTree(left, right, null) =>
            combineResults(left, right)
          case tree =>
            findModel(tree, ef, witnesses, constsToIgnore, depth + 1,
                      settings, searchDirector) match {
              case UnsatCertResult(subCert) => (pCert bindFirst subCert) match {
                case Left(newPCert) => {
                  pCert = newPCert
                  UnsatResult
                }
                case Right(totalCert) => {
                  UnsatCertResult(totalCert)
                }
              }
              case r@UnsatEFResult(formulae) => {
                ef = ef ++ formulae
                r
              }
              case r@EFRerunResult(formulae) => {
                ef = ef ++ formulae
                r
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
    val defConsts = arithModel.constants
    val addEqs =
      EquationConj(for (c <- literals.constants.iterator;
                        if (!(defConsts contains c)))
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
                            witnesses : List[ModelElement],
                            // explicitly quantified constants that do not have to
                            // be included in models
                            constsToIgnore : Set[ConstantTerm],
                            depth : Int,
                            settings : GoalSettings,
                            searchDirector : (Conjunction, Boolean) => SearchDirection)
                           : FindModelResult = {

    // The following functions are used to extract full models, possibly
    // resetting the constant freeness stored in the goal

    def addFormula(formula : Conjunction) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelSearchProver.AC, formula isSortedBy goal.order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      if (ModelElement.containAffectedSymbols(List(formula), witnesses))
        EFRerunResult(List(formula))
      else
        findModel(goal, List(formula), witnesses, constsToIgnore, depth,
                  settings, searchDirector) match {
          case UnsatResult =>         UnsatEFResult(List(formula))
          case UnsatEFResult(fors) => UnsatEFResult(List(formula) ++ fors)
          case UnsatCertResult(_) =>  throw new IllegalArgumentException
          case r =>                   r
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////

    def extractModel = searchDirector(goal.facts, false) match {
      case AcceptModelDir => {
        // should never happen
        assert(false)
        null
      }
      case DeriveFullModelDir => {
        // Check whether the theory plugin can give us a model
        val theoryModel =
          for (plugin <- Param.THEORY_PLUGIN(settings);
               m <- plugin generateModel goal) yield m

        val model = if (theoryModel.isDefined) {
          // replace the facts with the model, and continue
          // proving to take care of other possible predicates
          // in the goal

          val newSettings =
            Param.GARBAGE_COLLECTED_FUNCTIONS.set(
              Param.THEORY_PLUGIN.set(settings, None),
              Set())
          val newGoal = Goal(Conjunction.TRUE, CompoundFormulas.EMPTY(Map()),
                             TaskManager.EMPTY ++ (
                               goal formulaTasks theoryModel.get.negate),
                             goal.age,
                             goal.eliminatedConstants,
                             goal.vocabulary,
                             goal.definedSyms,
                             goal.branchInferences,
                             newSettings)
          val res = findModel(newGoal,
                              List(), witnesses, constsToIgnore, depth,
                              newSettings, FullModelDirector)

          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
          // We should be able to derive a counterexample
          Debug.assertPost(ModelSearchProver.AC, res match {
                             case ModelResult(model) => !model.isFalse
                             case _ => false
                           })
          //-END-ASSERTION-///////////////////////////////////////////////////////
          res.asInstanceOf[ModelResult].model
        } else if (goal.constantFreedom.isBottom) {
          // we have already found a model
        
          val order = goal.order
          assembleModel(ModelElement.constructModel(witnesses, order),
                        goal.facts.predConj, constsToIgnore, order)
        } else {
          // We have to lower the constant freedom, to make sure that
          // quantified formulae are fully taken into account when building
          // the model.
          
          // TODO: this could probably be done much more efficiently
          // TODO: the proof generation could be switched off from this point on
        
          val res = findModel(goal updateConstantFreedom ConstantFreedom.BOTTOM,
                              List(), witnesses, constsToIgnore, depth,
                              settings, FullModelDirector)

          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
          // We should be able to derive a counterexample
          Debug.assertPost(ModelSearchProver.AC, res match {
                             case ModelResult(model) => !model.isFalse
                             case _ => false
                           })
          //-END-ASSERTION-///////////////////////////////////////////////////////
          res.asInstanceOf[ModelResult].model
        }
        
        searchDirector(model, true) match {
          case DeriveFullModelDir => {
            // should never happen
            assert(false)
            null
          }
          case ReturnSatDir =>           SatResult
          case NextModelDir =>           UnsatResult
          case AcceptModelDir =>         ModelResult(model)
          case AddFormulaDir(formula) => addFormula(formula)
        }
      }
        
      case ReturnSatDir =>           SatResult
      case NextModelDir =>           UnsatResult
      case AddFormulaDir(formula) => addFormula(formula)
    }

    ////////////////////////////////////////////////////////////////////////////

    if (!goal.facts.arithConj.positiveEqs.isTrue &&
        !goal.constantFreedom.isBottomWRT(goal.facts.arithConj.positiveEqs.constants)) {

      // When constructing proofs, it can happen that not all
      // equations can be eliminated. We have to make sure that this
      // does not have any consequences for the created instantiations
      // of quantified formulae
    	
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelSearchProver.AC, Param.PROOF_CONSTRUCTION(settings))
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val lowerConstantFreedom =
        goal.constantFreedom.findNonFreeness(
          Conjunction.conj(goal.facts.arithConj, goal.order).negate,
          goal.bindingContext)

      findModel(goal updateConstantFreedom lowerConstantFreedom, List(),
   	            witnesses, constsToIgnore, depth, settings, searchDirector)

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

      // for the time being, just disable possible theory plugins at this point
      val newSettings = Param.THEORY_PLUGIN.set(settings, None)

      val newGoal = Goal(Conjunction.TRUE, CompoundFormulas.EMPTY(Map()),
                         TaskManager.EMPTY ++ (goal formulaTasks newFacts.negate),
                         goal.age,
                         goal.eliminatedConstants,
                         goal.vocabulary,
                         goal.definedSyms,
                         goal.branchInferences,
                         newSettings)

//    	nonRemovingPTF.updateGoal(Conjunction.TRUE, CompoundFormulas.EMPTY,
//    			                  goal formulaTasks newFacts.negate, goal)

      var doExtractModel = false
      var outerResult : FindModelResult = null

      findModel(newGoal, List(), witnesses, Set(), depth, newSettings, {
        
        case (_, false) =>
          // now we can actually be sure that we have found a genuine model,
          // let's ask the search director
          searchDirector(goal.facts, false) match {
            case AcceptModelDir => {
              // should never happen
              assert(false)
              null
            }
            case DeriveFullModelDir =>
              if (goal.constantFreedom.isBottom) {
                DeriveFullModelDir
              } else {
                doExtractModel = true
                ReturnSatDir
              }
            case ReturnSatDir => {
              outerResult = SatResult
              ReturnSatDir
            }
            case NextModelDir => {
              outerResult = UnsatResult
              ReturnSatDir
            }
            case AddFormulaDir(formula) => {
              outerResult = UnsatEFResult(List(formula))
              ReturnSatDir
            }
          }
        
        case (arithModel, true) => {
          val model = assembleModel(arithModel, goal.facts.predConj,
                                    constsToIgnore, goal.order)
          searchDirector(model, true) match {
            case DeriveFullModelDir => {
              // should never happen
              assert(false)
              null
            }
            case ReturnSatDir => {
              outerResult = SatResult
              ReturnSatDir
            }
            case NextModelDir => {
              outerResult = UnsatResult
              ReturnSatDir
            }
            case AcceptModelDir => {
              outerResult = ModelResult(model)
              ReturnSatDir
            }
            case AddFormulaDir(formula) => {
              outerResult = UnsatEFResult(List(formula))
              ReturnSatDir
            }
          }
        }
        
      }) match {
        
        case SatResult =>
          if (doExtractModel) {
            // The goal is satisfiable, and we can extract a counterexample.
            // However, due to the free-constant optimisation, 
            // we might have to perform further splitting, etc. to construct a
            // genuine counterexample
            
            extractModel
          } else {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(ModelSearchProver.AC, outerResult != null)
            //-END-ASSERTION-///////////////////////////////////////////////////
            outerResult match {
              case UnsatEFResult(List(formula)) => addFormula(formula)
              case r => r
            }
          }
          
        case r => r
          
      }

    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Prover that can be used incrementally
  
  def emptyIncProver(rawSettings : GoalSettings) : IncProver = {
    val settings = Param.APPLY_BLOCKED_TASKS.set(rawSettings, true)
    new IncProver(Goal(List(), Set(), Vocabulary(TermOrder.EMPTY), settings),
                  settings)
  }
  
  class IncProver protected[proof] (goal : Goal,
                                    settings : GoalSettings) {

    def order : TermOrder = goal.order
    
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
        if (newOrder eq goal.order) {
          goal
        } else {
          val oldConsts = goal.order.orderedConstants
          val newConsts = {
            val builder = ArrayBuilder.make[ConstantTerm]
            val it = newOrder.orderedConstants.iterator
            while (it.hasNext) {
              val c = it.next
              if (!(oldConsts contains c))
                builder += c
            }
            builder.result
          }
            //newOrder.orderedConstants -- goal.order.orderedConstants
            
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
      
      new IncProver(resGoal, settings)
    }

    def checkValidity(constructModel : Boolean) : Either[Conjunction, Certificate] =
      if (constructModel)
        checkValidityDir(FullModelDirector)
      else
        checkValidityDir(SatOnlyDirector)

    def checkValidityDir(searchDirector : (Conjunction, Boolean) => SearchDirection)
                     : Either[Conjunction, Certificate] =
      findModel(goal, List(), List(), Set(), 0, settings,
                searchDirector) match {
        case SatResult                      => Left(Conjunction.TRUE)
        case ModelResult(model)             => Left(model)
        case UnsatResult | UnsatEFResult(_) => Left(Conjunction.FALSE)
        case UnsatCertResult(cert)          => Right(cert)
        case EFRerunResult(_)               => // should never happen
                                               throw new IllegalArgumentException
      }

    /**
     * Apply a simple criterion to check whether the formulas so far
     * are valid
     */
    def isObviouslyValid : Boolean = goal.facts.isFalse

    /**
     * Apply a simple criterion to check whether the formulas so far
     * are not valid (there are still countermodels)
     */
    def isObviouslyUnprovable : Boolean =
      !goal.facts.isFalse &&
      goal.tasks.prioritisedTasks.isEmpty &&
      !Param.THEORY_PLUGIN(goal.settings).isDefined && {
        val facts = goal.facts
        val ac = facts.arithConj
        val inEqConsts = ac.inEqs.constants

        (facts.predConj.isTrue ||
           (goal.compoundFormulas.isEmpty &&
              Seqs.disjoint(facts.predConj.predicates,
                            Param.FUNCTIONAL_PREDICATES(goal.settings)))) &&
        (ac.positiveEqs forall {
           lc => lc.leadingCoeff.isOne && {
                   val c = lc.leadingTerm.asInstanceOf[ConstantTerm]
                   !(inEqConsts contains c) &&
                   !(ac.negativeEqs.constants contains c) &&
                   !(facts.predConj.constants contains c)
                 }
         }) &&
        ac.inEqs.isObviouslySat &&
        (ac.negativeEqs forall {
           lc => lc.constants exists { c => !(inEqConsts contains c) }
         }) &&
        Seqs.disjoint(facts.predConj.constants, inEqConsts)
      }

    /**
     * Eliminate all prioritised tasks for which the given predicate is false.
     */
    def filterTasks(p : PrioritisedTask => Boolean) : IncProver = {
      val newGoal = goal filterTasks p
      if (newGoal eq goal)
        this
      else
        new IncProver(newGoal, settings)
    }
  }
  
}

 
private case class WitnessTree(val subtree : ProofTree,
                               val modelElement : ModelElement,
                               val vocabulary : Vocabulary)
                   extends { protected val subtreeOrder = vocabulary.order }
                           with ProofTreeOneChild {

  def update(newSubtree : ProofTree, newConstantFreedom : ConstantFreedom) : ProofTree =
    new WitnessTree(subtree, modelElement,
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
