/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof;

import ap._
import ap.basetypes.IdealInt
import ap.terfor.{Formula, TermOrder, ConstantTerm, OneTerm}
import ap.terfor.arithconj.{ArithConj, ModelElement}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.substitutions.{Substitution, IdentitySubst}
import ap.terfor.preds.PredConj
import ap.proof.goal.{Goal, NegLitClauseTask, AddFactsTask, CompoundFormulas,
                      TaskManager, PrioritisedTask}
import ap.proof.certificates.{Certificate, CertFormula, PartialCertificate,
                              LemmaBase, BranchInferenceCertificate,
                              TheoryAxiomInference}
import ap.theories.{GroebnerMultiplication, Theory}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree._
import ap.proof.theoryPlugins.{Plugin, PluginSequence}
import ap.util.{Debug, Logic, LRUCache, FilterIt, Seqs, Timeout, OpCounters}

import scala.collection.mutable.ArrayBuilder

/**
 * A prover that tries to construct a countermodel of a ground formula. This
 * prover works in depth-first mode, in contrast to the
 * <code>ExhaustiveProver</code>.
 */
object ModelSearchProver {

  private val AC = Debug.AC_PROVER
  private val simplifier = ConstraintSimplifier.FAIR_SIMPLIFIER
   
  val DEFAULT = new ModelSearchProver(GoalSettings.DEFAULT)

  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>FALSE</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  def apply(inputFor : Formula, order : TermOrder) : Conjunction =
    DEFAULT(inputFor, order)

  /**
   * <code>inputDisjuncts</code> are the formulae (connected disjunctively) to
   * be disproven. The result of the method is either countermodel of
   * <code>inputDisjuncts</code> (the case <code>Left</code>), or a proof of
   * validity (<code>Right</code>). In case proof construction is disabled,
   * the validity result will be <code>Left(FALSE)</code>.
   */
  def apply(inputDisjuncts : Seq[Conjunction],
            order : TermOrder,
            settings : GoalSettings,
            withFullModel : Boolean = true) : Either[Conjunction, Certificate] =
    (new ModelSearchProver(settings))(inputDisjuncts, order, withFullModel)

  //////////////////////////////////////////////////////////////////////////////

  private sealed abstract class FindModelResult
  private case object SatResult                         extends FindModelResult
  private case object UnsatResult                       extends FindModelResult
  private case class  UnsatEFResult(extraFFors : Seq[Conjunction])
                                                        extends FindModelResult
  // because of new formulas that were added, we have to redo part of the proof
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
  // Prover that can be used incrementally
  
  def emptyIncProver(rawSettings : GoalSettings) : IncProver = {
    val settings = Param.APPLY_BLOCKED_TASKS.set(rawSettings, true)
    val (goal, certFormulas) =
      Goal.createWithCertFormulas(List(), Set(),
                                  Vocabulary(TermOrder.EMPTY), settings)
    val p = new ModelSearchProver(settings)
    new p.IncProverImpl(goal, certFormulas)
  }

  abstract class IncProver {
    def order : TermOrder
    def assert(f : Conjunction, newOrder : TermOrder) : IncProver
    def assert(fors : Iterable[Conjunction],
               newOrder : TermOrder) : IncProver
    def conclude(f : Conjunction, newOrder : TermOrder) : IncProver
    def conclude(fors : Iterable[Conjunction],
                 newOrder : TermOrder) : IncProver
    def checkValidity(constructModel : Boolean)
                     : Either[Conjunction, Certificate]
    def checkValidityDir(searchDirector
                          : (Conjunction, Boolean) => SearchDirection)
                     : Either[Conjunction, Certificate]
    def checkValidityDir(searchDirector
                          : (Conjunction, Boolean) => SearchDirection,
                         lemmaBase : LemmaBase)
                     : Either[Conjunction, Certificate]
                     
    /**
     * Apply a simple criterion to check whether the formulas so far
     * are valid
     */
    def isObviouslyValid : Boolean

    /**
     * Apply a simple criterion to check whether the formulas so far
     * are not valid (there are still countermodels)
     */
    def isObviouslyUnprovable : Boolean

    /**
     * Eliminate all prioritised tasks for which the given predicate is false.
     */
    def filterTasks(p : PrioritisedTask => Boolean) : IncProver
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * A prover that tries to construct a countermodel of a ground formula. This
 * prover works in depth-first mode, in contrast to the
 * <code>ExhaustiveProver</code>.
 */
class ModelSearchProver(defaultSettings : GoalSettings) {
  import ModelSearchProver._

  private val randomDataSource = Param.RANDOM_DATA_SOURCE(defaultSettings)

  // we need to store eliminated facts from goals, otherwise we could not
  // construct a complete model
  private val ptf = new SimpleProofTreeFactory(true, simplifier,
                                               randomDataSource) {
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
                order, defaultSettings, FullModelDirector).left.get
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
  def apply(inputDisjuncts : Seq[Conjunction],
            order : TermOrder,
            withFullModel : Boolean = true)
            : Either[Conjunction, Certificate] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ModelSearchProver.AC,
                  inputDisjuncts forall ((inputFor) =>
                    inputFor.variables.isEmpty && (order isSortingOf inputFor)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    applyHelp(inputDisjuncts, order,
              Param.CONSTRAINT_SIMPLIFIER.set(defaultSettings, simplifier),
              if (withFullModel) FullModelDirector else SatOnlyDirector)
  }
   
  /**
   * <code>inputFor</code> is the formula to be disproven. The result of the
   * method is a countermodel of <code>inputFor</code>, or <code>None</code>
   * if it was not possible to find one (this implies that <code>inputFor</code>
   * is valid).
   */
  private def applyHelp(disjuncts : Seq[Conjunction],
                        order : TermOrder,
                        rawSettings : GoalSettings,
                        searchDirector
                          : (Conjunction, Boolean) => SearchDirection)
                       : Either[Conjunction, Certificate] = {
    val settings = Param.APPLY_BLOCKED_TASKS.set(rawSettings, true)
    val elimConstants = order.orderedConstants
    val vocabulary =
      Vocabulary(order,
                 BindingContext.EMPTY.addAndContract(elimConstants, Quantifier.ALL),
                 ConstantFreedom.BOTTOM addTopStatus elimConstants)
    val (goal, certFormulas) =
      Goal.createWithCertFormulas(disjuncts, elimConstants,
                                  vocabulary, settings)
    val lemmaBase : LemmaBase =
      if (Param.PROOF_CONSTRUCTION(settings)) {
        val printL = Param.LOG_LEVEL(settings) contains Param.LOG_LEMMAS
        val base = new LemmaBase(printLemmas = printL)
        base assumeFormulas certFormulas.iterator
        base
      } else {
        null
      }

    findModel(goal, List(), List(), Set(), 0, settings, searchDirector,
              lemmaBase, 0) match {
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
        Debug.assertInt(ModelSearchProver.AC,
                        Param.PROOF_CONSTRUCTION(settings))
        //-END-ASSERTION-///////////////////////////////////////////////////////

        /*
         * Some code to identify dangling formulae (assumed formulae that were
         * never provided) in a certificate
         *

        val badFormulas =
          cert.assumedFormulas --
          (for (d <- disjuncts.iterator) yield CertFormula(d.negate)).toSet
        if (!badFormulas.isEmpty) {
          println("FINISHED, but certificate makes incorrect assumptions:")
          println(badFormulas)
          throw new IllegalArgumentException
        }

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
                        verifyCertificate(cert, disjuncts))
        //-END-ASSERTION-///////////////////////////////////////////////////////
          
        Right(cert)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def verifyCertificate(cert : Certificate,
                                disjuncts : Seq[Conjunction]) : Boolean = {
 
    // verify assumptions
    (cert.assumedFormulas subsetOf
      (for (d <- disjuncts.iterator) yield CertFormula(d.negate)).toSet) &&
    //
    // verify theory axioms
    (true || SimpleAPI.withProver { p =>
      import p._

      def traverse(c : Certificate) : Boolean =
        (c match {
          case BranchInferenceCertificate(inferences, _, order) =>
            inferences forall {
              case TheoryAxiomInference(axiom, GroebnerMultiplication) =>
                scope {
                  Console.err.println("Verifying: " + axiom)
                  addTheory(GroebnerMultiplication)
                  addConclusion(axiom.toConj)
                  
                  try {
                    withTimeout(3000) {
                      ??? match {
                        case SimpleAPI.ProverStatus.Valid =>
                          true
                        case _ =>
                          Console.err.println("FAILED")
                          true
                      }
                    }
                  } catch {
                    case SimpleAPI.TimeoutException =>
                      Console.err.println("T/O")
                      true
                  }
                }
              case _ =>
                true
            }
          case _ =>
            true
         }) &&
        (c.subCertificates forall (traverse _))

      traverse(cert)
    })
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
                        searchDirector : (Conjunction, Boolean) => SearchDirection,
                        // lemma base used for storing certificates, or
                        // <code>null</code>
                        lemmaBase : LemmaBase,
                        lemmaBaseAssumedInferences : Int)
                       : FindModelResult = {
    Timeout.check
    
    tree match {
      case goal : Goal if !extraFormulae.isEmpty => {
        // there are some further formulae to be added to be goal before
        // we continue with the proof
          
        val (uGoal, _) =
          goal addTasksFor (
                    for (f <- extraFormulae) yield (goal reduceWithFacts f))

        findModel(uGoal,
                  List(), witnesses,
                  constsToIgnore, depth, settings, searchDirector,
                  lemmaBase, lemmaBaseAssumedInferences) match {
          case r@EFRerunResult(formulas) =>
            EFRerunResult(extraFormulae ++ formulas)
          case r@UnsatEFResult(formulas) =>
            UnsatEFResult(extraFormulae ++ formulas)
          case r => r
        }
      }

      case goal : Goal => {
        // we use a loop to apply rules to this proof goal

        var result : FindModelResult            = null
        var newGoal : Goal                      = goal
        var newLemmaBaseAssumedInferences : Int = lemmaBaseAssumedInferences

        while (result == null) {
          val goal = newGoal

          // we might have to backtrack, if we are in an inconsistent state
          if (goal.facts.isFalse) {
            if (Param.LOG_LEVEL(settings) contains Param.LOG_BACKTRACKING)
              Console.err.println("Backtracking from level " + depth)

            OpCounters.inc(OpCounters.Backtrackings1)

            if (Param.PROOF_CONSTRUCTION(settings)) {
              val cert = goal.getCertificate
              //-BEGIN-ASSERTION-/////////////////////////////////////////////
              Debug.assertInt(ModelSearchProver.AC,
                lemmaBase == null ||
                ((lemmaBase allKnownWitness cert.assumedFormulas) match {
                    case Some(f) => {
                      throw new Exception(
                        "unasserted, but assumed formula: " + f +
                          " in certificate: " + cert)
                      false
                    }
                    case None =>
                      true
                 }))
              //-END-ASSERTION-///////////////////////////////////////////////
              return UnsatCertResult(cert)
            } else {
              return UnsatResult
            }
          }

          // take newly generated formulas into account in the lemma base
          if (lemmaBase != null) {
            val (formulaIt, newSize) =
              goal.branchInferences newProvidedFormulas
                                       newLemmaBaseAssumedInferences
            (lemmaBase assumeFormulas formulaIt) match {
              case Some(cert) =>
                return UnsatCertResult(goal.branchInferences.getCertificate(
                                         cert, goal.order))
              case None => // nothing
            }

            newLemmaBaseAssumedInferences = newSize
          }

          // if the constant freedom of the goal has changed, we need to
          // confirm the update
          if ((!goal.stepPossible ||
               (ExhaustiveProver ruleApplicationYield goal)) &&
              !goal.fixedConstantFreedom) {
            newGoal = goal updateConstantFreedom goal.closingConstantFreedom
          } else if (goal.stepPossible) {
            (goal step ptf) match {
              case g : Goal =>
                newGoal = g
              case newTree =>
                // the goal have turned into a more complicated tree,
                // do a recursive call
                result = findModel(newTree, List(), witnesses,
                                   constsToIgnore, depth, settings,
                                   searchDirector, lemmaBase,
                                   newLemmaBaseAssumedInferences)
            }
          } else {
            result = handleSatGoal(goal, witnesses, constsToIgnore, depth,
                                   settings, searchDirector,
                                   lemmaBase, newLemmaBaseAssumedInferences)
          }
        }

        result match {
          case EFRerunResult(formulas)
            if (!ModelElement.containAffectedSymbols(formulas, witnesses)) =>
            // we can start over from this point
            findModel(goal, formulas, witnesses,
                      constsToIgnore, depth, settings, searchDirector,
                      lemmaBase, newLemmaBaseAssumedInferences) match {
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
                  depth, settings, searchDirector,
                  lemmaBase, lemmaBaseAssumedInferences)

      case tree : ProofTreeOneChild => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ModelSearchProver.AC, tree match {
                          case _ : WeakenTree =>
                            false
                          case tree : QuantifiedTree =>
                            tree.quan == Quantifier.ALL
                          case _ =>
                            true
                        },
                        "unexpected proof tree in ModelSearchProver: " + tree)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val quanConsts = tree match {
          case tree : QuantifiedTree => tree.quantifiedConstants
          case _ => List()
        }
        val newConstsToIgnore = constsToIgnore ++ quanConsts

        val res =
          try {
            findModel(tree.subtree, extraFormulae, witnesses, newConstsToIgnore,
                      depth, settings, searchDirector,
                      lemmaBase, lemmaBaseAssumedInferences)
          } finally {
            if (lemmaBase != null)
              lemmaBase addObsoleteConstants quanConsts
          }

        res
      }

      case tree@AndTree(left, right, partialCert) if (partialCert != null) => {
        if (Param.LOG_LEVEL(settings) contains Param.LOG_SPLITS)
          Console.err.println("Splitting on level " + depth)

        OpCounters.inc(OpCounters.Splits1)

        var nonCertResult : FindModelResult = null

        val subCertBuilder = new PartialCertificate.CertBuilder {
          private var treeStack = List(left, right)

          private def extractNextChild : Unit = treeStack match {
            case AndTree(l, r, null) :: tail => {
              treeStack = l :: r :: tail
              extractNextChild
            }
            case _ => // nothing
          }

          def next = {
            extractNextChild
            val child = treeStack.head
            treeStack = treeStack.tail

            findModel(child, extraFormulae, witnesses, constsToIgnore,
                      depth + 1, settings, searchDirector, lemmaBase, 0) match {
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
          }

          def skipNext = {
            extractNextChild
            treeStack = treeStack.tail
          }
        }

        partialCert.dfExplore(subCertBuilder,
                              lemmaBase, lemmaBaseAssumedInferences) match {
          case null =>
            nonCertResult
          case res =>
            UnsatCertResult(res)
        }
      }
     
      case tree@AndTree(left, right, _) => {
        if (Param.LOG_LEVEL(settings) contains Param.LOG_SPLITS)
          Console.err.println("Splitting on level " + depth)

        OpCounters.inc(OpCounters.Splits1)

        findModel(left, extraFormulae, witnesses, constsToIgnore, depth + 1,
                  settings, searchDirector, null, 0) match {
          case UnsatResult =>
            findModel(right, extraFormulae, witnesses, constsToIgnore,
                      depth + 1, settings, searchDirector, null, 0)
          case r@UnsatEFResult(ef) =>
            findModel(right, extraFormulae ++ ef, witnesses, constsToIgnore,
                      depth + 1, settings, searchDirector, null, 0) match {
              case UnsatResult =>         r
              case UnsatEFResult(ef2) =>  UnsatEFResult(ef ++ ef2)
              case _ : UnsatCertResult =>
                throw new IllegalArgumentException("proof certificate missing")
              case r2 =>                  r2
            }
          case _ : UnsatCertResult =>
            throw new IllegalArgumentException("proof certificate missing")
          case lr => lr
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def assembleModel(basicModel : Conjunction,
                            literals : PredConj,
                            constsToIgnore : Set[ConstantTerm],
                            order : TermOrder) : Conjunction = {
    // assign constants not defined in the basic model to zero
    val defConsts = basicModel.constants
    val addEqs =
      EquationConj(for (c <- literals.constants.iterator;
                        if (!(defConsts contains c)))
                   yield LinearCombination(c, order),
                   order)

    val modelWithPreds =
      Conjunction.conj(Array(basicModel, addEqs, literals), order)

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

  /**
   * Handle a goal in which no further rule applications are possible.
   */
  private def handleSatGoal(goal : Goal,
                            // functions to reconstruct witnesses for eliminated
                            // constants
                            witnesses : List[ModelElement],
                            // explicitly quantified constants that do not have to
                            // be included in models
                            constsToIgnore : Set[ConstantTerm],
                            depth : Int,
                            settings : GoalSettings,
                            searchDirector
                               : (Conjunction, Boolean) => SearchDirection,
                            lemmaBase : LemmaBase,
                            lemmaBaseAssumedInferences : Int)
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
                  settings, searchDirector,
                  lemmaBase, lemmaBaseAssumedInferences) match {
          case UnsatResult =>         UnsatEFResult(List(formula))
          case UnsatEFResult(fors) => UnsatEFResult(List(formula) ++ fors)
          case UnsatCertResult(_) =>  throw new IllegalArgumentException
          case r =>                   r
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////

    def extractModel = searchDirector(goal.facts, false) match {
      case AcceptModelDir =>
        // should never happen
        throw new IllegalStateException
      case DeriveFullModelDir => {
        val model = if (!Param.MODEL_GENERATION(settings)) {

          // Need to make sure that the PresburgerModelfinder is
          // applied last!
          val newSettings =
            Param.PROOF_CONSTRUCTION.set(
              Param.THEORY_PLUGIN.set(
                Param.MODEL_GENERATION.set(settings, true),
                PluginSequence(Param.THEORY_PLUGIN(settings).toList ++
                                 List(new PresburgerModelFinder))),
              false)
          val newGoal = Goal(goal.facts,
                             goal.compoundFormulas,
                             TaskManager.EMPTY(newSettings),
                             goal.age,
                             goal.eliminatedConstants,
                             goal.vocabulary,
                             goal.definedSyms,
                             goal.branchInferences,
                             newSettings)
          val res = findModel(newGoal,
                              List(), witnesses, constsToIgnore, depth,
                              newSettings, FullModelDirector, null, 0)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // We should be able to derive a counterexample
          Debug.assertPost(ModelSearchProver.AC, res match {
                             case ModelResult(model) => !model.isFalse
                             case _ => false
                           })
          //-END-ASSERTION-/////////////////////////////////////////////////////
          res.asInstanceOf[ModelResult].model

        } else if (goal.constantFreedom.isBottom) {

          // we have already found a model
        
          val order = goal.order
          val predConj = goal.facts.predConj
          val initialPredModel =
            ((for (a <- predConj.positiveLits.iterator; if a.constants.isEmpty)
              yield (a -> true)) ++
             (for (a <- predConj.negativeLits.iterator; if a.constants.isEmpty)
              yield (a -> false))).toMap
            
          assembleModel(ModelElement.constructModel(witnesses, order,
                                                    Map(), initialPredModel),
                        predConj, constsToIgnore, order)

        } else {

          // We know that a model exists, but we still need to assign
          // values to leftover constants in the goal. We do this in such a
          // way that all predicate argument terms get pairwise different
          // values; in almost all cases (unless we have clauses applied
          // using unit resolution that compare predicate arguments in some
          // more complicated way) this should give us a model.

          val facts = goal.facts

          val assignmentFor =
            if (goal.constantFreedom isBottomWRT facts.predConj.constants) {
              List()
            } else {
              throw new Exception("theories failed to construct model for " + goal)

/*
              implicit val order = goal.order

              val terms =
                ((for (a <- facts.groundAtoms.iterator;
                       l <- a.iterator)
                  yield l) ++
                 (for (lc <- facts.arithConj.negativeEqs.iterator;
                       lc2 <- Iterator(
                                LinearCombination(lc.view(0, 1), order),
                                -LinearCombination(lc.view(1, lc.size), order)))
                  yield lc2)).toSet
              val assignment =
                PresburgerTools.distinctInterpretation(terms, order)

              List(
                Conjunction.negate(EquationConj(
                  for ((c, v) <- assignment.iterator;
                       if !(goal.constantFreedom isBottomWRT c))
                  yield LinearCombination(
                          Array((IdealInt.ONE, c), (-v, OneTerm)), order),
                  order), order))
 */
            }

          findModel(goal updateConstantFreedom ConstantFreedom.BOTTOM,
                    assignmentFor,
                    witnesses, constsToIgnore, depth,
                    settings, FullModelDirector,
                    null, 0) match {
            case ModelResult(model) if !model.isFalse =>
              model
            case r => {
              // That failed. We have to lower the constant freedom, to make
              // sure that quantified formulae are fully taken into account
              // when building the model.
              
              // TODO: this could probably be done much more efficiently
              // TODO: the proof generation could be switched off from this
              // point on
        println("fallback: " + r)
              val res =
                findModel(goal updateConstantFreedom ConstantFreedom.BOTTOM,
                          List(), witnesses, constsToIgnore, depth,
                          settings, FullModelDirector,
                          lemmaBase, lemmaBaseAssumedInferences)

              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              // We should be able to derive a counterexample
              Debug.assertPost(ModelSearchProver.AC, res match {
                                 case ModelResult(model) => !model.isFalse
                                 case _ => false
                               })
              //-END-ASSERTION-/////////////////////////////////////////////////
              res.asInstanceOf[ModelResult].model
            }
          }
        }
        
        searchDirector(model, true) match {
          case DeriveFullModelDir =>
            // should never happen
            throw new IllegalStateException
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
   	        witnesses, constsToIgnore, depth, settings, searchDirector,
                lemmaBase, lemmaBaseAssumedInferences)

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
                      !goal.facts.predConj.isTrue ||
                      !goal.compoundFormulas.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      // First continue proving only on arithmetic and basic propositional facts

      val order = goal.order

      val basicPredConj = goal.facts.predConj filter (_.constants.isEmpty)
      val newFacts = goal.facts.updatePredConj(basicPredConj)(order)

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

      val arithOnlyResult =
        findModel(newGoal, List(), witnesses, Set(), depth, newSettings, {
        
        case (_, false) =>
          // now we can actually be sure that we have found a genuine model,
          // let's ask the search director
          searchDirector(goal.facts, false) match {
            case AcceptModelDir =>
              // should never happen
              throw new IllegalStateException
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
        
        case (basicModel, true) => {
          val model = assembleModel(basicModel, goal.facts.predConj,
                                    constsToIgnore, goal.order)
          searchDirector(model, true) match {
            case DeriveFullModelDir =>
              // should never happen
              throw new IllegalStateException
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
        
      }, lemmaBase, lemmaBaseAssumedInferences)

      arithOnlyResult match {
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
  
  private class IncProverImpl(goal : Goal,
                              // certFormulas are needed for setting
                              // up the <code>LemmaBase</code>
                              certFormulas : Seq[CertFormula])
    extends IncProver {

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
                       goal.bindingContext.addAndContract(
                                                 newConsts, Quantifier.ALL),
                       goal.constantFreedom addTopStatus newConsts)

          nonRemovingPTF.updateGoal(goal.eliminatedConstants ++ newConsts,
                                    newVocabulary, List(),
                                    goal).asInstanceOf[Goal]
        }
      
      var (resGoal, additionalCertFormulas) = newOrderGoal addTasksFor fors

      // apply the most simple tasks right away
      // TODO: do this also for FactsNormalisationTask, UpdateTasksTask
      var cont = true
      while (cont && resGoal.stepPossible) {
        cont = resGoal.tasks.max match {
            case _ : NegLitClauseTask | _ : AddFactsTask => true
            case _ => false
          }
        if (cont)
          resGoal = (resGoal step ptf).asInstanceOf[Goal]
      }
      
      val newCertFormulas =
        if (certFormulas == null)
          null
        else
          certFormulas ++ additionalCertFormulas

      new IncProverImpl(resGoal, newCertFormulas)
    }

    def checkValidity(constructModel : Boolean)
                     : Either[Conjunction, Certificate] =
      if (constructModel)
        checkValidityDir(FullModelDirector)
      else
        checkValidityDir(SatOnlyDirector)

    def checkValidityDir(searchDirector
                          : (Conjunction, Boolean) => SearchDirection)
                     : Either[Conjunction, Certificate] = {
      val lemmaBase =
        if (certFormulas == null)
          null
        else
          new LemmaBase
      checkValidityDir(searchDirector, lemmaBase)
    }

    def checkValidityDir(searchDirector
                          : (Conjunction, Boolean) => SearchDirection,
                         lemmaBase : LemmaBase)
                     : Either[Conjunction, Certificate] = {
      if (lemmaBase != null)
        lemmaBase assumeFormulas certFormulas.iterator

      findModel(goal, List(), List(), Set(), 0, defaultSettings,
                searchDirector, lemmaBase, 0) match {
        case SatResult                      => Left(Conjunction.TRUE)
        case ModelResult(model)             => Left(model)
        case UnsatResult | UnsatEFResult(_) => Left(Conjunction.FALSE)
        case UnsatCertResult(cert)          => Right(cert)
        case EFRerunResult(_)               => // should never happen
                                              throw new IllegalArgumentException
      }
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
        new IncProverImpl(newGoal, certFormulas)
    }
  }
  
}

////////////////////////////////////////////////////////////////////////////////
 
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

////////////////////////////////////////////////////////////////////////////////

private class PresburgerModelFinder extends Plugin {

  import Plugin.{AddFormula, SplitGoal}
  import Conjunction.conj

  override def toString : String = "PresburgerModelFinder"

  private val AC = Debug.AC_PROVER

  private val rand = new SeededRandomDataSource(54321)

  override def computeModel(goal : Goal) : Seq[Plugin.Action] = {

    goalState(goal) match {
      case Plugin.GoalState.Final =>
        strengthenBounds(goal) elseDo pickPredicateArguments(goal)
      case _ =>
        List()
    }
  }

  /**
   * If a proof goal still contains arithmetic formulas, we compute a
   * model by systematically strengthening inequalities. Since we have
   * already established that the goal of satisfiable, this is
   * guaranteed to yield a model.
   * 
   * TODO: this is probably quite slow and should be optimized.
   */
  private def strengthenBounds(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts
    val inEqs = facts.arithConj.inEqs
    val o     = goal.order

    if (inEqs.isEmpty)
      return List()

    // val lc = inEqs.geqZero.minBy(_.constant.abs)
    val lc = inEqs(rand.nextInt(inEqs.geqZero.size))

    List(SplitGoal(List(List(AddFormula(conj(NegEquationConj(lc, o), o))),
                        List(AddFormula(conj(EquationConj(lc, o), o))))))
  }
  
  /**
   * Assign values to the remaining constants in such a way that
   * predicate arguments all become pairwise distinct, and that
   * disequalities are satisfied.
   */
  private def pickPredicateArguments(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts
    val order = goal.order

    val (mgAtoms, otherAtoms) =
      facts.predConj partition { a => Theory.isModelGenPredicate(a.pred) }
    val avoidedConsts =
      (for (a <- mgAtoms.iterator; c <- a.constants.iterator) yield c).toSet

    val terms =
      ((for (a <- facts.groundAtoms.iterator;
             l <- a.iterator;
             if Seqs.disjoint(l.constants, avoidedConsts))
        yield l) ++
         (for (lc <- facts.arithConj.negativeEqs.iterator;
               if Seqs.disjoint(lc.constants, avoidedConsts);
               lc2 <- Iterator(
                 LinearCombination(lc.view(0, 1), order),
                 -LinearCombination(lc.view(1, lc.size), order)))
          yield lc2)).toSet

    val assignment = PresburgerTools.distinctInterpretation(terms, order)

    if (assignment.isEmpty) {
      List()
    } else {
      List(
        Plugin.AddFormula(
          Conjunction.negate(EquationConj(
            for ((c, v) <- assignment.iterator)
            yield LinearCombination(
                    Array((IdealInt.ONE, c), (-v, OneTerm)), order),
                    order), order)))
    }
  }

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
