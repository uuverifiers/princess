/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.proof._
import ap.terfor.{Formula, ConstantTerm, VariableTerm,
                  TermOrder, TerFor, Term, AliasChecker}
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions,
                               ReduceWithConjunction, Quantifier}
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.{PredConj, Atom}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.{Substitution, IdentitySubst}
import ap.util.{Debug, FilterIt, Logic, Seqs}
import ap.parameters.{GoalSettings, Param}
import ap.proof.tree.{ProofTree, ProofTreeFactory}
import ap.proof.certificates.{Certificate, CloseCertificate,
                              BranchInferenceCollection,
                              BranchInferenceCollector,
                              NonLoggingBranchInferenceCollector,
                              CertCompoundFormula, CertFormula}

import scala.collection.immutable.VectorBuilder

object Goal {
  
  private val AC = Debug.AC_GOAL

  def apply(facts : Conjunction, compoundFormulas : CompoundFormulas,
            tasks : TaskManager, age : Int,
            eliminatedConstants : Set[ConstantTerm], vocabulary : Vocabulary,
            definedSyms : Substitution,
            branchInferences : BranchInferenceCollection,
            settings : GoalSettings) : Goal =
    if (facts.isFalse)
      TRUE(vocabulary, branchInferences)
    else
      new Goal(facts, compoundFormulas, tasks, age, eliminatedConstants,
               vocabulary, definedSyms, branchInferences, settings)

  def reduceAndCreateGoal(f : Formula, order : TermOrder, settings : GoalSettings) : Goal =
    reduceAndCreateGoal(f, Set.empty, order, settings)

  def reduceAndCreateGoal(f : Formula,
                          eliminatedConstants : Set[ConstantTerm],
                          order : TermOrder,
                          settings : GoalSettings) : Goal = {
    val reducer = ReduceWithConjunction(Conjunction.TRUE,
                                        order,
                                        Param.REDUCER_SETTINGS(settings))
    apply(List(reducer(Conjunction.conj(f, order))),
          eliminatedConstants, Vocabulary(order), settings)
  }

  def createWithCertFormulas(initialConjs : Seq[Conjunction],
                             eliminatedConstants : Set[ConstantTerm],
                             vocabulary : Vocabulary,
                             settings : GoalSettings)
                            : (Goal, Seq[CertFormula]) = {
    val tasks =
      (for (c <- initialConjs.iterator;
            t <- formulaTasks(c, 0, eliminatedConstants,
                              vocabulary, settings).iterator) yield t).toList

    val (certFormulas, initialInfCollection) =
      if (Param.PROOF_CONSTRUCTION(settings)) {
        val certFormulas = for (c <- initialConjs) yield CertFormula(c.negate)
        (certFormulas, BranchInferenceCollection applyCert certFormulas)
      } else {
        (null, BranchInferenceCollection.EMPTY)
      }

    val emptyTaskManager = TaskManager EMPTY settings

    val goal =
      apply(Conjunction.TRUE,
            CompoundFormulas.EMPTY(Param.PREDICATE_MATCH_CONFIG(settings)),
            emptyTaskManager ++ tasks,
            0,
            eliminatedConstants,
            vocabulary,
            new IdentitySubst (vocabulary.order),
            initialInfCollection,
            settings)

    (goal, certFormulas)
  }

  def apply(initialConjs : Seq[Conjunction],
            eliminatedConstants : Set[ConstantTerm],
            vocabulary : Vocabulary,
            settings : GoalSettings) : Goal =
    createWithCertFormulas(initialConjs, eliminatedConstants,
                           vocabulary, settings)._1
  
  def TRUE(vocabulary : Vocabulary,
           branchInferences : BranchInferenceCollection) : Goal =
    new Goal (Conjunction.FALSE,
              CompoundFormulas.EMPTY(Map()),
              TaskManager.EMPTY, 0,
              Set.empty, vocabulary,
              new IdentitySubst (vocabulary.order),
              branchInferences,
              GoalSettings.DEFAULT)
  
  val TRUE : Goal = TRUE(Vocabulary.EMPTY, BranchInferenceCollection.EMPTY)
  
  /**
   * Create the tasks to store and handle an arbitrary given formula. This
   * method is part of the goal because different tasks might be created
   * depending on the settings
   */
  def formulaTasks(formula : Conjunction,
                   age : Int,
                   eliminatedConstants : Set[ConstantTerm],
                   vocabulary : Vocabulary,
                   settings : GoalSettings) : Seq[FormulaTask] =
    if (formula.isFalse) {
      List()
    } else if (formula.isTrue || formula.isLiteral) {
      List(new AddFactsTask(formula, age))
    } else if (formula.isNegatedConjunction) {
      val disj = formula.negatedConjs(0)
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // possibly existing quantifiers should have been pulled out and
      // should not occur at this point
      Debug.assertInt(Goal.AC, disj.quans.isEmpty)
      //-END-ASSERTION-///////////////////////////////////////////////////////

      var negLitClauses = List[Conjunction]()
      val otherTasks = new VectorBuilder[FormulaTask]
      val unitResolution = Param.POS_UNIT_RESOLUTION(settings)

      for (f <- disj.negatedConjs)
        if (unitResolution &&
            NegLitClauseTask.isCoveredFormula(f, settings))
          negLitClauses = f :: negLitClauses
        else
          otherTasks ++= formulaTasks(f, age, eliminatedConstants, vocabulary,
                                      settings)
        
      if (!negLitClauses.isEmpty)
        otherTasks +=
          NegLitClauseTask(Conjunction.disj(negLitClauses, formula.order), age,
                           settings)
 
      if (!disj.arithConj.isTrue || !disj.predConj.isTrue) {
        val facts = Conjunction(List(), disj.arithConj, disj.predConj,
                                NegatedConjunctions.TRUE, formula.order).negate
        otherTasks += new AddFactsTask(facts, age)
      }
       
      otherTasks.result
    } else if (formula.quans.isEmpty) {
      List(BetaFormulaTask(formula, age, eliminatedConstants, vocabulary,
                           settings))
    } else formula.quans.last match {
      case Quantifier.ALL => List(new AllQuantifierTask(formula, age))
      case Quantifier.EX => List(
        if (formula.isDivisibility)
          new DivisibilityTask(formula, age)
        else if (Param.POS_UNIT_RESOLUTION(settings) &&
                 NegLitClauseTask.isCoveredFormula(formula, settings))
          NegLitClauseTask(formula, age, settings)
        else
          new ExQuantifierTask(formula, age))
    }

}

class Goal private (val facts : Conjunction,
                    val compoundFormulas : CompoundFormulas,
                    val tasks : TaskManager,
                    val age : Int,
                    val eliminatedConstants : Set[ConstantTerm],
                    val vocabulary : Vocabulary,
                    val definedSyms : Substitution,
                    val branchInferences : BranchInferenceCollection,
                    val settings : GoalSettings) extends ProofTree {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Goal.AC,
                   // facts are really just literals (equations, inequalities,
                   // predicate literals)
                   facts.quans.isEmpty &&
                   facts.negatedConjs.isEmpty &&
                   // clauses are handled similar to facts; there are two
                   // kinds: quantified formulae that are instantiated
                   // through unit resolution with facts, and ground formulae
                   // that do not contain predicates or eliminated constants
                   // (splitting is unnecessary for such formulae)
                   compoundFormulas.qfClauses.forall((c) =>
                       constantFreedom.isShielded(c, bindingContext) ||
                       Seqs.disjoint(eliminatedConstants, c.constants) &&
                       Conjunction.collectQuantifiers(c).isEmpty) &&
                   // there should not be any free variables (use constants
                   // instead)
                   facts.variables.isEmpty &&
                   // if a contradiction is detected, we can forget about
                   // everything
                   (!facts.isFalse || tasks.isEmpty && compoundFormulas.isEmpty) &&
                   // contradictions of compound formulae should directly be
                   // propagated to the facts
                   !compoundFormulas.isFalse &&
                   // if clauses need to be rematched, a task for this should
                   // have been generated
                   (!compoundFormulas.lazyQuantifiedClauses.factsAreOutdated(facts.predConj) ||
                      !tasks.taskSummaryFor(TaskAggregator.LazyMatchTaskCounter).isEmpty ||
                     {
                       // alternatively, it might happen that the next rule
                       // application closes the goal
                       val nextTask = tasks.max
                       nextTask.isInstanceOf[AddFactsTask] &&
                         nextTask.asInstanceOf[AddFactsTask].formula == Conjunction.TRUE
                     }) &&
                   // we must choose an ordering such that the constants to be
                   // eliminated are maximal
                   (facts isSortedBy order) &&
                   (compoundFormulas isSortedBy order) &&
                   (definedSyms isSortedBy order) &&
                   (order constantsAreMaximal eliminatedConstants))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private def elimConstants(tfs : Seq[LinearCombination])
                          : Seq[LinearCombination] = {
    val res = new VectorBuilder[LinearCombination]
    for (tf <- tfs) {
      if (!tf.isEmpty && !(this eliminates tf.leadingTerm)) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(Goal.AC, Seqs.disjoint(tf.constants, eliminatedConstants))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        res += tf
      }
    }
    res.result
  }
  
  private def elimConstants(tfs : Iterator[LinearCombination])
                                                : Iterator[LinearCombination] =
    FilterIt(tfs, (tf:LinearCombination) => {
      val res = tf.isEmpty || !(this eliminates tf.leadingTerm)
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(Goal.AC,
                       res == Seqs.disjoint(tf.constants, eliminatedConstants))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    })
    
  private def arithClauses : NegatedConjunctions = compoundFormulas.qfClauses
  
  /**
   * In case the goal contains predicate literals, it might not be possible to
   * directly eliminate all constants to be eliminated
   */
  private lazy val constantEliminationPossible = {
    val ac = facts.arithConj
    val pc = facts.predConj
    Seqs.disjoint(eliminatedConstants, pc.constants, ac.negativeEqs.constants) &&
    Seqs.disjoint(eliminatedConstants, pc.constants, ac.inEqs.constants)
  }
  
  lazy val closingConstraint : Conjunction = {
    val ac = facts.arithConj
    
    // we can always leave out antecedent equations that contain eliminated
    // constants (because such equations can exhaustively be applied to all
    // other formulae)
    val selectedPosEqs =
      ac.positiveEqs.updateEqsSubset(elimConstants(ac.positiveEqs))(order)
    
    val selectedAC =
      if (constantEliminationPossible) {
        // then also succedent equations and inequalities that contain eliminated
        // constants can be left out

        val selectedNegEqs =
          ac.negativeEqs.updateEqsSubset(elimConstants(ac.negativeEqs))(order)
        val selectedInEqs =
          InEqConj(elimConstants(ac.inEqs.iterator ++
                                 ac.inEqs.geqZeroInfs.iterator),
                   order)

        ArithConj(selectedPosEqs, selectedNegEqs, selectedInEqs, order)
      } else {
        // otherwise, we have to consider all arithmetic literals, because
        // rules like OmegaElim or SplitEq are not applicable in the presence
        // of predicate literals, and the calculus is thus not complete for
        // eliminating constants
        
        ac.updatePositiveEqs(selectedPosEqs)(order)
      }

    val selectedConj =
      definedSyms(Conjunction(List(), selectedAC, PredConj.TRUE, arithClauses,
                              order)).negate
    val res = constantFreedom.unshieldedPart(selectedConj, bindingContext)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Goal.AC, order isSortingOf res)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  lazy val closingConstantFreedom : ConstantFreedom =
    if (constantEliminationPossible &&
        constantFreedom.isBottomWRT(constants -- eliminatedConstants))
      // if only eliminated constants are free constants, it is not possible
      // that the constant freedom changes
      constantFreedom
   else
      constantFreedom.findNonFreeness(closingConstraint, bindingContext)

  lazy val fixedConstantFreedom : Boolean =
    constantFreedom == closingConstantFreedom

  lazy val mayAlias : AliasChecker =
    new AliasAnalyser (reduceWithFacts,
                       constantFreedom, vocabulary.bindingContext,
                       order)
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * All constants that occur in formulas in this goal
   */
  lazy val constants : Set[ConstantTerm] =
    facts.constants ++ compoundFormulas.constants ++ tasks.taskConstants
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Return whether <code>t</code> is a constant that is eliminated in this goal
   */
  def eliminates(t : Term) : Boolean = t match {
    case t : ConstantTerm => eliminatedConstants contains t
    case _ => false
  }

  lazy val reducerSettings = Param.REDUCER_SETTINGS(settings)

  lazy val reduceWithFacts : ReduceWithConjunction =
    ReduceWithConjunction(facts, order, reducerSettings)
  
  /**
   * Constants that can be eliminated in this goal because they are
   * universal, and they do not occur in any tasks or compound formulas
   * (but they might occur in the facts)
   */
  lazy val eliminatedIsolatedConstants : Set[ConstantTerm] =
    eliminatedConstants --tasks.taskConstants --compoundFormulas.constants
 
  //////////////////////////////////////////////////////////////////////////////

  val stepPossible : Boolean = !tasks.isEmpty

  val stepMeaningful : Boolean = stepPossible
  
  def step(ptf : ProofTreeFactory) : ProofTree = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Goal.AC, this.stepPossible)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    // apply the first task to the goal and then stop immediately
    val task = tasks.max

//    println(task)
    
//    task match {
//      case WrappedFormulaTask(t, Seq(simpTask)) => println("" + simpTask + " <- " + t)
//      case t => println(t)
//   }
    
//    ap.util.Timer.measure((WrappedFormulaTask unwrapReal task).getClass.getName) {
      task(this, ptf)
//    }
  }

  /**
   * Create the tasks to store and handle an arbitrary given formula. This
   * method is part of the goal because different tasks might be created
   * depending on the settings
   */
  def formulaTasks(formula : Conjunction) : Seq[FormulaTask] =
    Goal.formulaTasks(formula, age, eliminatedConstants, vocabulary, settings)
      
  def updateConstantFreedom(cf : ConstantFreedom) : Goal =
    if (constantFreedom == cf) {
      this
    } else if (facts.isFalse) {
      // then it is meaningless to generate a new task, instead we just
      // change the vocabulary of the goal
      Goal.TRUE(vocabulary updateConstantFreedom cf, branchInferences)
    } else {
      Goal(facts, compoundFormulas,
           tasks ++ List(new UpdateConstantFreedomTask(cf, age)), age,
           eliminatedConstants, vocabulary, definedSyms, branchInferences,
           settings)
    }
  
  /**
   * Generate tasks for the given formulas and add them to the goal
   */
  def addTasksFor(fors : Iterable[Conjunction]) : (Goal, Seq[CertFormula]) =
    if (facts.isFalse) {
      // new tasks are useless in this case; we have to be careful
      // not to delete the stored inferences
      (this, List())
    } else {
      val newTasks = for (f <- fors; t <- formulaTasks(f)) yield t
    
      val collector = getInferenceCollector
      val certFormulas =
        if (collector.isLogging) {
          val certFormulas = (for (f <- fors) yield CertFormula(f.negate)).toSeq
          for (f <- certFormulas) collector newCertFormula f
          certFormulas
        } else {
          null
        }

      (Goal(facts, compoundFormulas, tasks ++ newTasks, age,
            eliminatedConstants, vocabulary, definedSyms,
            collector.getCollection, settings),
       certFormulas)
    }
  
  /**
   * Eliminate all prioritised tasks for which the given predicate is false.
   */
  def filterTasks(p : PrioritisedTask => Boolean) : Goal = {
    val newTasks = tasks filter p
    if (newTasks eq tasks)
      this
    else
      Goal(facts, compoundFormulas, newTasks, age,
           eliminatedConstants, vocabulary, definedSyms, branchInferences,
           settings)
  }

  def getInferenceCollector : BranchInferenceCollector =
    if (Param.PROOF_CONSTRUCTION(settings))
      branchInferences.getCollector
    else
      NonLoggingBranchInferenceCollector
  
  /**
   * Function to be called after split rules, to generate new inference
   * collections for the subgoals. All compound formulae introduced by the split
   * rule (formulae that are not literals) have to be given as arguments.
   */
  def startNewInferenceCollection(initialFors : => Iterable[Conjunction])
                                 : BranchInferenceCollection =
    if (Param.PROOF_CONSTRUCTION(settings))
      BranchInferenceCollection(initialFors)
    else
      BranchInferenceCollection.EMPTY
  
  def startNewInferenceCollectionCert(initialFors : => Iterable[CertFormula])
                                 : BranchInferenceCollection =
    if (Param.PROOF_CONSTRUCTION(settings))
      BranchInferenceCollection applyCert initialFors
    else
      BranchInferenceCollection.EMPTY
  
  def startNewInferenceCollection : BranchInferenceCollection =
    if (Param.PROOF_CONSTRUCTION(settings))
      BranchInferenceCollection(List[Conjunction]())
    else
      BranchInferenceCollection.EMPTY
  
  def getCertificate : Certificate =
    branchInferences.getCertificate(
      if (facts.isFalse) {
        val contradFor =
          branchInferences.findFalseFormula
                          .getOrElse(CertCompoundFormula(Conjunction.FALSE))
        CloseCertificate(Set(contradFor), order)
      } else {
        // In the presence of predicates, it can happen that a sub-proof was used
        // to show the inconsistency of the arithmetic facts. We currently just
        // call the ModelSearchProver to construct a certificate, this should
        // be generalised

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(Goal.AC, !facts.predConj.isTrue)
        //-END-ASSERTION-///////////////////////////////////////////////////////
      
        val factDisjuncts = (for (l <- facts.arithConj.iterator)
                               yield Conjunction.conj(l.negate, order)).toList
        ModelSearchProver(factDisjuncts, order, settings).right.get
      }, order)
    
  //////////////////////////////////////////////////////////////////////////////
  
  val subtrees : Seq[ProofTree] = List()
  
  override def toString : String = {
    "^ " + closingConstraint + "\n" +
    ". Facts: " + facts + "\n" +
    ". Arithmetic clauses: " + compoundFormulas.qfClauses + "\n" +
    ". Eagerly matched clauses: " + compoundFormulas.eagerQuantifiedClauses + "\n" +
    ". Lazily matched clauses: " + compoundFormulas.lazyQuantifiedClauses + "\n" +
    ". Tasks: " + tasks + "\n" +
    ". Eliminated constants: " + eliminatedConstants + "\n" +
    ". Free constants " + (if (fixedConstantFreedom) "(fixed)" else "(not fixed)") +
                     ": " + constantFreedom + "\n" +
    ". Defined constants: " + definedSyms + "\n" +
    ". Stored inferences: " + branchInferences
  }
}
