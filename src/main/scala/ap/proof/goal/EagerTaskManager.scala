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

package ap.proof.goal;

import ap.proof.theoryPlugins.{Plugin, EagerPluginTask, PrioritisedPluginTask,
                               IntermediatePluginTask}


/**
 * A class for tracking the application of tasks and recommending the
 * intermediate application of <code>EagerTask</code>s. This class is
 * implemented as a finite automaton to give recommendations based on the
 * history of task applications
 */
abstract class EagerTaskManager {

  /**
   * Tell the manager that a certain task was applied
   */
  def afterTask(task : Task) : EagerTaskManager

  /**
   * Obtain a recommendation from the manager, given the next
   * <code>PrioritisedTask</code> in the queue. If the queue is empty,
   * <code>None</code> should be given as argument
   */
  def recommend(nextPrioritisedTask : Option[PrioritisedTask])
               : Option[EagerTask]
  
  /**
   * Check whether rule applications for this goal are finished
   * (with possible exception of prover plugin application)
   */
  def atFinal : Boolean

}

////////////////////////////////////////////////////////////////////////////////

object EagerTaskAutomaton {

  private def unwrapRealOption(npt : Option[PrioritisedTask]) = npt match {
    case Some(WrappedFormulaTask(realTask, _)) => Some(realTask)
    case _ => npt
  }
  
}

class EagerTaskAutomaton(plugin : Option[Plugin]) {

  import WrappedFormulaTask.{unwrapReal, MaybeWrapped}
  import EagerTaskAutomaton.unwrapRealOption
  
  /**
   * Abstract superclass for the task managers that are currently used (to
   * factor out common functionality)
   */
  private abstract class DefaultEagerTaskManager
                           (recommendedTask : Option[EagerTask],
                            checkBetaSimpTasks : Boolean)
                         extends EagerTaskManager {
    def recommend(npt : Option[PrioritisedTask]) = npt match {
      case None =>
        recommendedTask
      case Some(WrappedFormulaTask(_ : BetaFormulaTask, simpTasks))
        if (checkBetaSimpTasks &&
            (simpTasks exists (!recommendationNecessary(_)))) =>
        None
      case Some(MaybeWrapped(t)) if (recommendationNecessary(t)) =>
        recommendedTask
      case _ =>
        None
    }

    def atFinal : Boolean = false

    protected def recommendationNecessary(t : Task) : Boolean
  }
  
  /**
   * It is unknown whether the facts of the current goal are normalised
   */
  private object NonNormalisedFacts
                 extends DefaultEagerTaskManager(Some(FactsNormalisationTask),
                                                 false) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask
            if (plugin.isDefined) => NormalisedFactsInvokePlugin
      case FactsNormalisationTask => NormalisedFacts
      case _ =>                      NonNormalisedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BetaFormulaTask |
           _ : ExQuantifierTask |
           _ : DivisibilityTask |
           _ : LazyMatchTask |
           _ : IntermediatePluginTask |
           _ : BoundStrengthenTask |
           _ : PrioritisedPluginTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * It is known that <code>FactsNormalisationTask</code> has been applied,
   * and the facts of the current goal are normalised; the theory plugin
   * should be applied next
   */
  private object NormalisedFactsInvokePlugin
                 extends DefaultEagerTaskManager(
                           for (p <- plugin) yield (new EagerPluginTask(p)),
                           true) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case _ : AddFactsTask =>    NonNormalisedFacts
      case _ : EagerPluginTask => NormalisedFacts
      case _ =>                   NormalisedFactsInvokePlugin
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BetaFormulaTask |
           _ : ExQuantifierTask |
           _ : DivisibilityTask |
           _ : LazyMatchTask |
           _ : IntermediatePluginTask |
           _ : PrioritisedPluginTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * It is known that <code>FactsNormalisationTask</code> has been applied, the
   * facts of the current goal are normalised, and (if present) the theory
   * plugin has been called
   */
  private object NormalisedFacts
                 extends DefaultEagerTaskManager(Some(UpdateTasksTask),
                                                 true) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case _ : AddFactsTask =>   NonNormalisedFacts
      case UpdateTasksTask =>    NormalisedFactsAndTasks 
      case _ =>                  NormalisedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BetaFormulaTask |
           _ : ExQuantifierTask |
           _ : DivisibilityTask |
           _ : LazyMatchTask |
           _ : IntermediatePluginTask |
           _ : PrioritisedPluginTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * It is known that <code>FactsNormalisationTask</code> has been applied, the
   * facts of the current goal are normalised, and also
   * <code>UpdateTasksTask</code> has been applied so that all tasks are
   * normalised
   */
  private object NormalisedFactsAndTasks
                 extends DefaultEagerTaskManager(Some(EagerMatchTask),
                                                 true) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case _ : AddFactsTask =>   NonNormalisedFacts
      case EagerMatchTask =>     MatchedEagerClauses
      case _ =>                  NormalisedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BetaFormulaTask |
           _ : ExQuantifierTask |
           _ : LazyMatchTask |
           _ : IntermediatePluginTask |
           _ : PrioritisedPluginTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * It is known that <code>FactsNormalisationTask</code> has been applied, the
   * facts of the current goal are normalised, and also
   * <code>UpdateTasksTask</code> has been applied so that all tasks are
   * normalised. In addition, eagerly matched clauses have been instantiated.
   */
  private object MatchedEagerClauses
                 extends DefaultEagerTaskManager(Some(EliminateFactsTask),
                                                 true) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask | EliminateFactsTask => ReducedFacts
      case _ : AddFactsTask =>                            NonNormalisedFacts
      case _ : UpdateConstantFreedomTask =>               NormalisedFacts
      case _ : NegLitClauseTask =>                        NormalisedFactsAndTasks
      case _ =>                                           MatchedEagerClauses
    }
    
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BetaFormulaTask |
           _ : ExQuantifierTask |
           _ : LazyMatchTask |
           _ : IntermediatePluginTask |
           _ : PrioritisedPluginTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }
  
  /**
   * It is known that <code>FactsNormalisationTask</code> and
   * <code>EliminateFactsTask<code> have been applied, but it could have
   * happened that afterwards constants have disappeared from the tasks in the
   * queue, so that further eliminations might be possible
   */
  private object ProbablyReducedFacts
                 extends DefaultEagerTaskManager(Some(EliminateFactsTask),
                                                 false) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask | EliminateFactsTask => ReducedFacts
      case _ : AddFactsTask =>                            NonNormalisedFacts
      case _ : UpdateConstantFreedomTask =>               NormalisedFacts
      case _ : NegLitClauseTask =>                        NormalisedFactsAndTasks
      // all other tasks could result in the disappearance of constants in
      // the task queue, which could make it necessary to apply
      // <code>EliminateFactsTask</code> again
      case _ =>                                           ProbablyReducedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : ExQuantifierTask |
           _ : DivisibilityTask |
           _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * It is known that both <code>FactsNormalisationTask</code> and
   * <code>EliminateFactsTask<code> have been applied, the
   * facts of the current goal are normalised and unnecessary facts have been
   * removed (with respect to the current tasks)
   */
  private object ReducedFacts
                 extends DefaultEagerTaskManager(Some(OmegaTask),
                                                 false) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask |
           EliminateFactsTask =>             ReducedFacts
      case _ : AddFactsTask =>               NonNormalisedFacts
      case _ : UpdateConstantFreedomTask =>  NormalisedFacts
      case _ : NegLitClauseTask =>           NormalisedFactsAndTasks
      case OmegaTask =>                      if (plugin.isDefined) FinalInvokePlugin
                                             else Final
      // all other tasks could result in the disappearance of constants in
      // the task queue, which could make it necessary to apply
      // <code>EliminateFactsTask</code> again
      case _ =>                              ProbablyReducedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BlockedFormulaTask => true
      case _ => false
    }
  }

  /**
   * Everything is done, but we should try to invoke the prover
   * plugin once more
   */
  private object FinalInvokePlugin
                 extends DefaultEagerTaskManager(
                            for (p <- plugin) yield (new EagerPluginTask(p)),
                            true) {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask | EliminateFactsTask => ReducedFacts
      case _ : EagerPluginTask =>                         Final
      case _ : AddFactsTask =>                            NonNormalisedFacts
      case _ : UpdateConstantFreedomTask =>               NormalisedFacts
      // all other tasks could result in the disappearance of constants in
      // the task queue, which could make it necessary to apply
      // <code>EliminateFactsTask</code> again
      case _ =>                                           ProbablyReducedFacts
    }
    protected def recommendationNecessary(t : Task) = t match {
      case _ : BlockedFormulaTask => true
      case _ => false
    }
    override def atFinal : Boolean = true
  }

  /**
   * The final state in where there is nothing left to do. This state can be
   * reached by applying the task <code>OmegaTask</code>. In case that actually
   * an equation was split, this will lead to <code>AddFactsTask</code>, and the
   * state will be left again immediately
   */
  private object Final extends EagerTaskManager {
    def afterTask(task : Task) = unwrapReal(task) match {
      case FactsNormalisationTask | EliminateFactsTask => ReducedFacts
      case OmegaTask | _ : BlockedFormulaTask =>          Final
      case _ : AddFactsTask =>                            NonNormalisedFacts
      case _ : UpdateConstantFreedomTask =>               NormalisedFacts
      // all other tasks could result in the disappearance of constants in
      // the task queue, which could make it necessary to apply
      // <code>EliminateFactsTask</code> again
      case _ =>                                           ProbablyReducedFacts
    }
    def recommend(npt : Option[PrioritisedTask]) = None    
    def atFinal : Boolean = true
  }
   
  /**
   * In the beginning, there are no facts, which are thus reduced
   */
  val INITIAL : EagerTaskManager =
    if (plugin.isDefined) FinalInvokePlugin else Final

}
