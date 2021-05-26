/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2021 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.theoryPlugins;

import ap.basetypes.IdealInt
import ap.theories.Theory
import ap.proof.goal.{Goal, Task, EagerTask, PrioritisedTask}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates._
import ap.terfor.{Formula, TermOrder, TerForConvenience, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ReducableModelElement
import ap.parameters.{Param, ReducerSettings}
import ap.util.Debug

import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.{Stack, ArrayBuffer}

object Plugin {
  protected[theoryPlugins] val AC = Debug.AC_PLUGIN

  abstract sealed class Action

  /**
   * Add a formula to the handled proof goal. This action does not
   * support generation of proof certificates.
   */
  case class AddFormula  (formula : Conjunction)    extends Action

  /**
   * Remove some facts from the handled proof goal.
   */
  case class RemoveFacts (facts : Conjunction)      extends Action

  /**
   * Record that values of the given constants can be reconstructed from
   * the provided facts.
   */
  case class AddReducableModelElement
                         (facts : Conjunction,
                          constants : Set[ConstantTerm],
                          reducerSettings : ReducerSettings)
                                                    extends Action
  
  /**
   * Split a proof goal into multiple sub-goals. This action does not
   * support generation of proof certificates.
   */
  case class SplitGoal   (cases : Seq[Seq[Action]]) extends Action
  
  /**
   * Close the goal by invoking an explicit theory axiom.
   * The action can specify a list of assumptions that are antecedents
   * of the axiom and assumed to be present in a goal. Constants in the
   * axiom will be replaced with universally quantified variables.
   */
  case class CloseByAxiom(assumptions : Seq[Formula],
                          theory : Theory)          extends Action

  /**
   * Add an explicit theory axiom. The action can specify a list of
   * assumptions that are antecedents of the axiom and assumed
   * to be present in a goal. Constants in the axiom will be replaced
   * with universally quantified variables.
   */
  case class AddAxiom    (assumptions : Seq[Formula],
                          axiom : Conjunction,
                          theory : Theory)          extends Action
  
  /**
   * Split a proof goal into multiple sub-goals, and justify the split
   * through an explicit theory axiom. The action can specify a list of
   * assumptions that are antecedents of the axiom, but already assumed
   * to be present in a goal. Constants in the axiom will be replaced
   * with universally quantified variables.
   */
  case class AxiomSplit  (assumptions : Seq[Formula],
                          cases : Seq[(Conjunction, Seq[Action])],
                          theory : Theory)          extends Action

  /**
   * Split a disequality fact into two inequalities.
   */
  case class SplitDisequality(equality : LinearCombination,
                              leftActions : Seq[Action],
                              rightActions : Seq[Action]) extends Action
  
  /**
   * Schedule a task to be applied later on the goal.
   */
  case class ScheduleTask(proc : TheoryProcedure,
                          priority : Int)           extends Action

  /**
   * A simple relevance filter to get rid of axioms that follow trivially
   * from built-in arithmetic rules. Such irrelevant axioms should not be
   * added, since they might interfere with the built-in simplification rules,
   * and sometimes lead to illformed proofs.
   */
  def isRelevantAxiomAction(action : Action,
                            order : TermOrder) : Boolean = action match {
    case AddAxiom(assumptions, axiom, _) => {
      implicit val o = order
      import TerForConvenience._

      !(conj(assumptions) ==> axiom).isTrue
    }
    case AxiomSplit(assumptions, cases, _) => {
      implicit val o = order
      import TerForConvenience._

      !(conj(assumptions) ==> disj(for ((a, _) <- cases) yield a)).isTrue
    }
    case _ =>
      true
  }

  object GoalState extends Enumeration {
    val Intermediate, Final = Value
  }
}

/**
 * General interface for a theory-specific procedure that
 * can be applied by a prover to reason about interpreted symbols.
 */
trait TheoryProcedure {

  import Plugin.GoalState

  /**
   * Apply this procedure to the given goal.
   */
  def handleGoal(goal : Goal) : Seq[Plugin.Action]

  /**
   * Try to determine in which state a given goal is.
   */
  def goalState(goal : Goal) : GoalState.Value =
    if (goal.tasks.finalEagerTask) GoalState.Final else GoalState.Intermediate

  /**
   * An implicit function to simplify cascading of possible actions.
   */
  protected implicit def richActionSeq(acts : Seq[Plugin.Action]) =
    new RichActionSeq(acts)

  class RichActionSeq(acts : Seq[Plugin.Action]) {
    def elseDo(otherwise : => Seq[Plugin.Action]) : Seq[Plugin.Action] =
      if (acts.isEmpty) otherwise else acts
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Interface for theory plugins that can be added to the
 * <code>EagerTaskManager</code>. At the moment, such plugins
 * can mainly observe which formulae are asserted on a branch,
 * and then generate/instantiate further axioms to add
 * theory knowledge.
 *
 * Plugin objects have to be immutable.
 */
trait Plugin extends TheoryProcedure {

  /**
   * Given the current goal, possible generate (local and global) axioms.
   */
  def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)]

  /**
   * Apply this plugin to the given goal. The default procedure
   * is to call <code>generateAxioms</code>, and possibly add further
   * facts or axioms to the goal.
   */
  def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    generateAxioms(goal) match {
      case Some((localAxioms, globalAxioms)) => {
        val allAxioms = Conjunction.conj(List(localAxioms, globalAxioms),
                                         goal.order).negate
        List(Plugin.AddFormula(allAxioms))
      }
      case None =>
        List()
    }

  /**
   * Check whether the formulas in the given goal are satisfiable,
   * and if yes generate a model. The returned
   * formula is meant to replace the goal facts in this case.
   */
  def generateModel(goal : Goal) : Option[Conjunction] = None

}

////////////////////////////////////////////////////////////////////////////////

object PluginSequence {
  def apply(plugins : Seq[Plugin]) : Option[Plugin] = plugins match {
    case Seq()       => None
    case Seq(plugin) => Some(plugin)
    case plugins     => {
      val flatPlugins =
        for (p <- plugins;
             q <- p match {
               case p : PluginSequence => p.plugins
               case p => List(p)
             })
        yield q
      Some(new PluginSequence(flatPlugins))
    }
  }
}

/**
 * Execution of a sequence of plugins.
 */
class PluginSequence private (val plugins : Seq[Plugin]) extends Plugin {

  // not used
  def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
    throw new UnsupportedOperationException

  override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    val it = plugins.iterator
    val res = new VectorBuilder[Plugin.Action]
    var cont = true
    while (cont && it.hasNext) {
      val newActions = it.next handleGoal goal
      res ++= newActions
      cont = !splittingActions(newActions)
    }
    res.result
  }

  private def splittingActions(actions : Seq[Plugin.Action]) =
    actions exists {
      case _ : Plugin.SplitGoal        => true
      case _ : Plugin.CloseByAxiom     => true
      case _ : Plugin.AxiomSplit       => true
      case _ : Plugin.SplitDisequality => true
      case _ =>                           false
    }

  /**
   * Check whether the formulas in the given goal are satisfiable,
   * and if yes generate a model. The returned
   * formula is meant to replace the goal facts in this case.
   */
  override def generateModel(goal : Goal) : Option[Conjunction] = {
    val it = plugins.iterator
    var res : Option[Conjunction] = None
    while (!res.isDefined && it.hasNext)
      res = it.next generateModel goal
    res
  }

}

////////////////////////////////////////////////////////////////////////////////

object PluginTask {

  /**
   * Split assumptions into compound formulas, predicate atoms, and arithmetic
   * literals.
   */
  protected[ap] def prepareAssumptions(assumptions : Seq[Formula],
                                       alwaysNeedsQuantifiers : Boolean,
                                       order : TermOrder)
                        : (Seq[CertFormula],       // compoundAssumptions
                           Seq[CertFormula],       // predAssumptions
                           Seq[CertFormula]) = {   // arithAssumptions
    val needsQuantifiers =
      alwaysNeedsQuantifiers ||
      (assumptions exists (!_.constants.isEmpty))

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // There should not be any trivial assumptions, and no duplicate assumptions
    Debug.assertInt(Plugin.AC,
                    (assumptions forall { a => !a.isTrue }) &&
                    assumptions.size == assumptions.toSet.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // TODO: avoid conversion to conjunction
    val certAssumptions =
      for (a <- assumptions) yield CertFormula(Conjunction.conj(a, order))
    val (compoundAssumptions, simpleAssumptions) =
      certAssumptions partition (_.isInstanceOf[CertCompoundFormula])
    val (predAssumptions, arithAssumptions) =
      if (needsQuantifiers)
        simpleAssumptions partition (_.isInstanceOf[CertPredLiteral])
      else
        (List(), simpleAssumptions)

    (compoundAssumptions, predAssumptions, arithAssumptions)
  }

  /**
   * Generate the inferences needed to introduce a theory axiom.
   * <code>instAxiom</code> is the instantiated axiom, but excluding
   * assumed predicate literals (given as <code>predAssumptions</code>).
   */
  protected[ap] def axiomInferences(instAxiom : CertFormula,
                                    predAssumptions : Seq[CertFormula],
                                    theory : Theory)
                                   (implicit order : TermOrder)
                                  : Seq[BranchInference] = {
    val predLits =
      for (f <- predAssumptions) yield f.asInstanceOf[CertPredLiteral]
    val negPredLits =
      predLits map { l => !l }
    val instAxiomWithPreds =
      Conjunction.disj(List(instAxiom.toConj) ++ (negPredLits map (_.toConj)),
                       order)
    val consts =
      (order sort instAxiomWithPreds.constants).reverse

    val (axiom, instInf) =
      if (consts.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(Plugin.AC, predAssumptions.isEmpty)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        (instAxiom, List())
      } else {
        val axiomConj =
          Conjunction.quantify(Quantifier.ALL, consts, instAxiomWithPreds,order)
        val axiom =
          CertFormula(axiomConj).asInstanceOf[CertCompoundFormula]
        val instanceTerms =
          for (c <- consts) yield LinearCombination(c, order)

        (axiom,
         List(GroundInstInference(axiom, instanceTerms,
                                  CertFormula(instAxiomWithPreds),
                                  predLits, instAxiom, order)))
      }

    List(TheoryAxiomInference(axiom, theory)) ++ instInf
  }

  /**
   * Generate the certificate steps needed to discharge the
   * given (atomic) arithmetic or predicate assumptions.
   */
  protected[ap] def proveSimpleAssumptions(assumptions : Seq[CertFormula])
                                          (implicit order : TermOrder)
                                         : Seq[(CertFormula, Certificate)] =
    for (a <- assumptions) yield {
      val inf = simpleAssumptionInf(a)
      val ccert = CloseCertificate(Set(inf.providedFormulas.head), order)
      (!a, BranchInferenceCertificate.prepend(List(inf), ccert, order))
    }

  protected[ap] def simpleAssumptionInf(assumption : CertFormula)
                                       (implicit order : TermOrder)
                                      : BranchInference = assumption match {
        case eq : CertEquation =>
          ReduceInference(List((IdealInt.MINUS_ONE, eq)), !eq, order)
        case eq : CertNegEquation =>
          ReduceInference(List((IdealInt.MINUS_ONE, !eq)), eq, order)
        case ineq : CertInequality => {
          val negIneq = !ineq
          val result = CertInequality(ineq.lhs + negIneq.lhs)
          CombineInequalitiesInference(IdealInt.ONE, ineq,
                                       IdealInt.ONE, negIneq,
                                       result, order)
        }
        case l : CertPredLiteral =>
          PredUnifyInference(l.atom, l.atom, 
                             CertFormula(Conjunction.TRUE), order)
        case _ : CertCompoundFormula =>
          throw new IllegalArgumentException
      }

}

/**
 * Task integrating a <code>Plugin</code> (or <code>TheoryProcedure</code>)
 * into a prover
 */
abstract class PluginTask(plugin : TheoryProcedure) extends Task {
  import Plugin._

  def apply(goal : Goal, ptf : ProofTreeFactory) : ProofTree = {
    val actions = plugin handleGoal goal

    if (actions.isEmpty)
      ptf.updateGoal(goal)
    else if (Param.PROOF_CONSTRUCTION(goal.settings))
      handleActionsRec(actions.toList, List(), goal, goal.branchInferences, ptf)
    else
      handleActionsNonCert(actions, goal, ptf)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def handleActionsRec(actions : List[Action],
                               contActions : List[Action],
                               goal : Goal,
                               branchInferences : BranchInferenceCollection,
                               ptf : ProofTreeFactory) : ProofTree =
    actions match {

      case List() =>
        applyActions(contActions, goal, branchInferences, ptf)

      case AddAxiom(assumptions, f, theory) :: rest =>
         handleActionsRec(
           List(AxiomSplit(assumptions,
                           if (f.isFalse) List() else List((f, rest)),
                           theory)),
           contActions, goal, branchInferences, ptf)

      case CloseByAxiom(assumptions, theory) :: rest =>
         handleActionsRec(
           List(AxiomSplit(assumptions, List(), theory)),
           contActions, goal, branchInferences, ptf)

      case List(AxiomSplit(assumptions, cases, theory)) => {
        implicit val order = goal.order

        import PluginTask.{prepareAssumptions, axiomInferences,
                           proveSimpleAssumptions}

        val (compoundAssumptions, predAssumptions, arithAssumptions) =
          prepareAssumptions(
             assumptions,
             cases exists { case (f, _) => !f.constants.isEmpty },
             order)

        (arithAssumptions.size, cases.size + compoundAssumptions.size) match {

          // a case where we can just add the axiom using an inference;
          // no assumptions
          case (0, 1) if compoundAssumptions.isEmpty => {
            val Seq((axiomCase, rest)) =
              cases
            val newInferences =
              branchInferences ++
              axiomInferences(CertFormula(axiomCase),
                              predAssumptions, theory)
            handleActionsRec(rest.toList,
                             AddFormula(!axiomCase) :: contActions,
                             goal,
                             newInferences,
                             ptf)
          }

          // a case where we can just add the axiom using an inference;
          // only an assumption, no cases
          case (0, 1) => {
            val Seq(assumption) =
              compoundAssumptions
            val negA =
              !assumption
            val newInferences =
              branchInferences ++
              axiomInferences(negA, predAssumptions, theory)
            applyActions(AddFormula(assumption.toConj) :: contActions,
                         goal,
                         newInferences,
                         ptf)
          }

          // the case where we can just add the axiom using an inference
          // encapsulating a partial certificate
          // (<code>PartialCertificateInference</code>)
          case (_, 1) => {
            val (providedFormula, addedFormula, restActions) =
              compoundAssumptions match {
                case Seq(assumption) =>
                  (!assumption, assumption.toConj, List())
                case Seq() => {
                  val Seq((axiomCase, rest)) = cases
                  (CertFormula(axiomCase), !axiomCase, rest.toList)
                }
              }

            // certificate constructor, to be applied once the goal has
            // been closed
            def comb(certs : Seq[Certificate]) : Certificate = {
              // add proofs for the simple assumptions
              val simpleCerts =
                proveSimpleAssumptions(arithAssumptions)
              val allCerts =
                simpleCerts ++ List((providedFormula, certs.head))
              val (instAxiom, betaCert) =
                BetaCertificate.naryWithDisjunction(allCerts, order)
    
              BranchInferenceCertificate.prepend(
                  axiomInferences(instAxiom, predAssumptions, theory),
                  betaCert, order)
            }
            
            val pCert =
              PartialCertificate(comb _, List(Set(providedFormula)))
            val pCertInf =
              PartialCertificateInference(pCert,
                                          Set(providedFormula),
                                          Set())

            val newInferences = branchInferences addWithDefaultInfs pCertInf

            handleActionsRec(restActions,
                             AddFormula(addedFormula) :: contActions,
                             goal,
                             newInferences,
                             ptf)
          }

          // the case where we can directly close this proof branch
          // (but have to discharge the made assumptions)
          case (_, 0) => {
            // certificate constructor that ignores the certificates coming
            // from the dummy leafs
            def comb(certs : Seq[Certificate]) : Certificate = {
              // add proofs for the simple assumptions
              val (inferences, betaCert) =
                if (arithAssumptions.isEmpty) {
                  val allCerts =
                    proveSimpleAssumptions(predAssumptions ++ arithAssumptions)
                  val (instAxiom, betaCert) =
                    BetaCertificate.naryWithDisjunction(allCerts, order)
                  (axiomInferences(instAxiom, List(), theory),
                   betaCert)
                } else {
                  val allCerts =
                    proveSimpleAssumptions(arithAssumptions)
                  val (instAxiom, betaCert) =
                    BetaCertificate.naryWithDisjunction(allCerts, order)
                  (axiomInferences(instAxiom, predAssumptions, theory),
                   betaCert)
                }

              BranchInferenceCertificate.prepend(inferences, betaCert, order)
            }
    
            val pCert = PartialCertificate(comb _, dummyProvidedFormulas,
                                           branchInferences, order)
            ptf.andInOrder(dummySubTrees, pCert, goal.vocabulary)
          }

          // the case where proper proof splitting is needed
          case (_, caseNum) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(Plugin.AC, caseNum > 1)
            //-END-ASSERTION-///////////////////////////////////////////////////

            val subTrees =
              (for (a <- compoundAssumptions) yield {
                 applyActions(AddFormula(a.toConj) :: contActions,
                              goal,
                              goal startNewInferenceCollectionCert List(!a),
                              ptf)
               }) ++
              (for ((axiomCase, rest) <- cases) yield {
                 handleActionsRec(rest.toList,
                                  AddFormula(!axiomCase) :: contActions,
                                  goal,
                                  goal startNewInferenceCollection
                                                         List(axiomCase),
                                  ptf)
               })
    
            val providedFormulas =
              (for (a <- compoundAssumptions) yield Set(!a)) ++
              (for ((axiomCase, _) <- cases) yield Set(CertFormula(axiomCase)))

            // certificate constructor, to be applied once all sub-goals have
            // been closed
            def comb(certs : Seq[Certificate]) : Certificate = {
              // add proofs for the simple assumptions
              val simpleCerts =
                proveSimpleAssumptions(arithAssumptions)
              val allCerts =
                simpleCerts ++ ((providedFormulas map (_.head)) zip certs)
              val (instAxiom, betaCert) =
                BetaCertificate.naryWithDisjunction(allCerts, order)
    
              BranchInferenceCertificate.prepend(
                  axiomInferences(instAxiom, predAssumptions, theory),
                  betaCert, order)
            }
    
            val pCert =
              PartialCertificate(comb _, providedFormulas, branchInferences,
                                 order)

            ptf.andInOrder(subTrees, pCert, goal.vocabulary)
          }

        }
      }

      case List(SplitDisequality(eqLC, left, right)) => {
        implicit val order = goal.order
        import TerForConvenience._

        val leftSubtree =
          handleActionsRec(left.toList,
                           AddFormula(eqLC >= 0) :: contActions,
                           goal,
                           goal.startNewInferenceCollection,
                           ptf)
        val rightSubtree =
          handleActionsRec(right.toList,
                           AddFormula(eqLC <= 0) :: contActions,
                           goal,
                           goal.startNewInferenceCollection,
                           ptf)

        val leftInEq = CertInequality(-eqLC - 1)
        val rightInEq = CertInequality(eqLC - 1)

        // certificate constructor, to be applied once all sub-goals have
        // been closed
        def comb(certs : Seq[Certificate]) : Certificate =
          SplitEqCertificate(leftInEq, rightInEq, certs(0), certs(1), order)
        
        val pCert =
          PartialCertificate(comb _,
                             List(Set(leftInEq), Set(rightInEq)),
                             branchInferences, order)

        ptf.andInOrder(List(leftSubtree, rightSubtree), pCert, goal.vocabulary)
      }
     
      case AddReducableModelElement(facts, constants, settings) :: rest =>
        ptf.eliminatedConstant(handleActionsRec(rest, contActions, goal,
                                                branchInferences, ptf),
                               ReducableModelElement(facts, constants,
                                                     settings),
                               goal.vocabulary)
 
      case (a@(_ : RemoveFacts | _ : ScheduleTask)) :: rest =>
        handleActionsRec(rest, a :: contActions, goal, branchInferences, ptf)

      case actions =>
        throw new IllegalArgumentException("cannot execute actions " + actions)
    }

  private val dummySubTrees =
    List(Goal.TRUE, Goal.TRUE)
  private val dummyContradictionFors =
    Set(CertFormula(Conjunction.FALSE))
  private val dummyProvidedFormulas =
    List(dummyContradictionFors, dummyContradictionFors)


  //////////////////////////////////////////////////////////////////////////////
  
  private def handleActionsNonCert(actions : Seq[Action],
                                   goal : Goal,
                                   ptf : ProofTreeFactory) : ProofTree =
    actions.last match {
      case _ : SplitGoal | _ : AxiomSplit => {
        val actionStack    = new Stack[Seq[Action]]
        val resultingTrees = new ArrayBuffer[ProofTree]

        actionStack push actions

        while (!actionStack.isEmpty) {
          val actions = actionStack.pop
          if (actions.isEmpty) {
            resultingTrees += ptf.updateGoal(goal)
          } else actions.last match {
            case SplitGoal(subActions) => {
              val otherActions = actions.init
              for (b <- subActions.reverseIterator)
                actionStack push (otherActions ++ b)
            }
            case AxiomSplit(_, cases, _) => {
              val otherActions = actions.init
              for ((axiomCase, rest) <- cases.reverseIterator)
                actionStack push (otherActions ++
                                  List(AddFormula(!axiomCase)) ++
                                  rest)
            }
            case SplitDisequality(eqLC, left, right) => {
              implicit val order = goal.order
              import TerForConvenience._

              val otherActions = actions.init
              actionStack push (otherActions ++
                                List(AddFormula(eqLC <= 0)) ++
                                right)
              actionStack push (otherActions ++
                                List(AddFormula(eqLC >= 0)) ++
                                left)
            }
            case _ => {
              resultingTrees += applyActions(actions, goal, null, ptf)
            }
          }
        }

        if (resultingTrees.isEmpty)
          applyActions(List(AddFormula(Conjunction.TRUE)), goal, null, ptf)
        else
          ptf.andInOrder(resultingTrees.toSeq, goal.vocabulary)
      }

      case _ =>
        applyActions(actions, goal, null, ptf)
    }

  //////////////////////////////////////////////////////////////////////////////
  
  private def applyActions(actions : Seq[Action],
                           goal : Goal,
                           branchInferences : BranchInferenceCollection,
                           ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(Plugin.AC, !(actions exists (_.isInstanceOf[SplitGoal])))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val factsToRemove =
      Conjunction.conj(for (RemoveFacts(f) <- actions.iterator) yield f,
                       goal.order)

    val tasksToSchedule =
      (for (ScheduleTask(proc, priority) <- actions.iterator)
       yield new PrioritisedPluginTask(proc, priority, goal.age)).toList

    val formulaTasks =
      // if no inferences are given, we assume that proof generation is
      // disabled, so we are free to simplify
      if (branchInferences == null) {
        val newFormulas =
          for (action <- actions.iterator;
               if action.isInstanceOf[AddFormula] ||
                  action.isInstanceOf[AddAxiom] ||
                  action.isInstanceOf[CloseByAxiom])
          yield action match {
            case AddFormula(f) =>      f.negate
            case AddAxiom(_, f, _) =>  f
            case CloseByAxiom(_, _) => Conjunction.FALSE
            case _ => throw new IllegalArgumentException
        }

        val newForConj =
          goal reduceWithFacts Conjunction.conj(newFormulas, goal.order)

        goal formulaTasks newForConj.negate
      } else {
        for (a <- actions;
             t <- a match {
               case AddFormula(f) =>
                 goal formulaTasks f
               case AddAxiom(_, f, _) =>
                 goal formulaTasks f.negate
               case CloseByAxiom(_, _) =>
                 goal formulaTasks Conjunction.TRUE
               case _ =>
                 List()
             })
        yield t
      }

    // we have to be careful when removing facts; sometimes, removing facts
    // will lead to new facts being derived implicitly, because the number
    // of derived inequalities is bounded

    val (newFacts, newInferences) =
      if (factsToRemove.isTrue) {
        (goal.facts, branchInferences)
      } else {
        val logger =
          if (branchInferences == null)
            NonLoggingBranchInferenceCollector
          else
            branchInferences.getCollector
        val newFacts = goal.facts.remove(factsToRemove, logger)
        (newFacts, logger.getCollection)
      }

    val allFormulaTasks =
      if (formulaTasks.isEmpty &&
          (actions exists {
             case AddFormula(_) | RemoveFacts(_) | AddAxiom(_, _, _) => true
             case _ => false
           }) &&
          !newFacts.isTrue) {
        // we have to make sure that the plugin is called a a further time,
        // otherwise we get very confusing semantics
        // just add a formula that we already know about
        goal formulaTasks !newFacts.iterator.next
      } else {
        formulaTasks
      }

    val newTree =
      if (newInferences == null)
        ptf.updateGoal(newFacts,
                       tasksToSchedule ++ allFormulaTasks,
                       goal)
      else
        ptf.updateGoal(newFacts,
                       tasksToSchedule ++ allFormulaTasks,
                       newInferences,
                       goal)

    (actions.iterator :\ newTree) {
      case (AddReducableModelElement(f, consts, settings), t) =>
        ptf.eliminatedConstant(t, ReducableModelElement(f, consts, settings),
                               goal.vocabulary)
      case (_, t) =>
        t
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

class EagerPluginTask(plugin : TheoryProcedure)
      extends PluginTask(plugin) with EagerTask {
  override def toString = "EagerPluginTask(" + plugin + ")"
}

////////////////////////////////////////////////////////////////////////////////

class PrioritisedPluginTask(plugin : TheoryProcedure,
                            basePriority : Int,
                            age : Int)
      extends PluginTask(plugin) with PrioritisedTask {

  val priority : Int = basePriority + age
 
  /**
   * Update the task with possibly new information from the goal.
   * Currently, this does not modify the theory procedure.
   */
  def updateTask(goal : Goal, factCollector : Conjunction => Unit)
                                                   : Seq[PrioritisedTask] =
    List(this)

  override def toString = "PrioritisedPluginTask(" + plugin + ")"
}
