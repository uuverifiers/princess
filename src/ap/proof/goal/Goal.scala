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

package ap.proof.goal;

import scala.collection.mutable.ArrayBuffer

import ap.proof._
import ap.CmdlMain
import ap.terfor.{Formula, ConstantTerm, VariableTerm,
                  TermOrder, TerFor, Term, AliasStatus}
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
                              CCUCloseCertificate,
                              BranchInferenceCollection,
                              BranchInferenceCollector,
                              NonLoggingBranchInferenceCollector,
                              CertCompoundFormula, CertFormula}

object Goal {
  
  private val AC = Debug.AC_GOAL

  def apply(facts : Conjunction, compoundFormulas : CompoundFormulas,
            tasks : TaskManager, age : Int,
            eliminatedConstants : Set[ConstantTerm], vocabulary : Vocabulary,
            definedSyms : Substitution,
            branchInferences : BranchInferenceCollection,
            eliminatedEquations : List[EquationConj],
            settings : GoalSettings) : Goal =
    if (facts.isFalse)
      TRUE(vocabulary, branchInferences)
    else
      new Goal(facts, compoundFormulas, tasks, age, eliminatedConstants,
               vocabulary, definedSyms, branchInferences,
               eliminatedEquations, settings)

  def apply(facts : Conjunction, compoundFormulas : CompoundFormulas,
            tasks : TaskManager, age : Int,
            eliminatedConstants : Set[ConstantTerm], vocabulary : Vocabulary,
            definedSyms : Substitution,
            branchInferences : BranchInferenceCollection,
            settings : GoalSettings) : Goal =
    apply(facts, compoundFormulas, tasks, age, eliminatedConstants,
          vocabulary, definedSyms, branchInferences, List(), settings)

  def reduceAndCreateGoal(f : Formula, order : TermOrder, settings : GoalSettings) : Goal =
    reduceAndCreateGoal(f, Set.empty, order, settings)

  def reduceAndCreateGoal(f : Formula,
                          eliminatedConstants : Set[ConstantTerm],
                          order : TermOrder,
                          settings : GoalSettings) : Goal = {
    val reducer = ReduceWithConjunction(Conjunction.TRUE,
                                        Param.FUNCTIONAL_PREDICATES(settings),
                                        order)
    apply(List(reducer(Conjunction.conj(f, order))),
          eliminatedConstants, Vocabulary(order), settings)
  }
  
  def apply(initialConjs : Seq[Conjunction],
            eliminatedConstants : Set[ConstantTerm],
            vocabulary : Vocabulary,
            settings : GoalSettings) : Goal = {

    val tasks =
      (for (c <- initialConjs.iterator;
            t <- formulaTasks(c, 0, eliminatedConstants,
                              vocabulary, settings).iterator) yield t).toList

      // TODO: this has to be done in a more systematic manner
    val initialInfCollection = if (Param.PROOF_CONSTRUCTION(settings))
      BranchInferenceCollection(for (c <- initialConjs) yield c.negate)
    else
      BranchInferenceCollection.EMPTY

    val emptyTaskManager = Param.THEORY_PLUGIN(settings) match {
      case Some(plugin) => TaskManager EMPTY plugin
      case None         => TaskManager.EMPTY
    }

    apply(Conjunction.TRUE,
          CompoundFormulas.EMPTY(Param.FUNCTIONAL_PREDICATES(settings),
                                 Param.PREDICATE_MATCH_CONFIG(settings),
                                 !Param.CCU_SOLVER(settings).isDefined),
          emptyTaskManager ++ tasks,
          0,
          eliminatedConstants,
          vocabulary,
          new IdentitySubst (vocabulary.order),
          initialInfCollection,
          settings)
  }
  
  def TRUE(vocabulary : Vocabulary,
           branchInferences : BranchInferenceCollection) : Goal =
    new Goal (Conjunction.FALSE,
              CompoundFormulas.EMPTY(Map()),
              TaskManager.EMPTY, 0,
              Set.empty, vocabulary,
              new IdentitySubst (vocabulary.order),
              branchInferences, List(),
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

      {
        var negLitClauses = List[Conjunction]()
        val otherTasks = new ArrayBuffer[FormulaTask]
        val unitResolution = Param.POS_UNIT_RESOLUTION(settings)
        
        for (f <- disj.negatedConjs)
          if (unitResolution &&
              NegLitClauseTask.isCoveredFormula(f, settings))
            negLitClauses = f :: negLitClauses
          else
            otherTasks ++= formulaTasks(f, age, eliminatedConstants, vocabulary, settings)
        
        if (!negLitClauses.isEmpty)
          otherTasks +=
            NegLitClauseTask(Conjunction.disj(negLitClauses, formula.order), age,
                             settings)
        
        otherTasks
      } ++
      (if (disj.arithConj.isTrue && disj.predConj.isTrue) {
         List()
       } else {
         val facts = Conjunction(List(), disj.arithConj, disj.predConj,
                                 NegatedConjunctions.TRUE, formula.order).negate
         List(new AddFactsTask(facts, age))})
    } else if (formula.quans.isEmpty) {
      List(BetaFormulaTask(formula, age, eliminatedConstants, vocabulary, settings))
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
                    val eliminatedEquations : List[EquationConj],
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
                     tasks.taskInfos.containsLazyMatchTask ||
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

  private def elimConstants(tfs : Seq[LinearCombination]) : Seq[LinearCombination] = {
    val res = new ArrayBuffer[LinearCombination]
    for (tf <- tfs) {
      if (!tf.isEmpty && !(this eliminates tf.leadingTerm)) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(Goal.AC, Seqs.disjoint(tf.constants, eliminatedConstants))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        res += tf
      }
    }
    res
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

  val goalCount : Int = 1
  
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

  /**
   * For the CCU case, constant freedom is calculated using
   * the disequality propagation method.
   */
  lazy val ccuClosingConstantFreedom : ConstantFreedom =
    if (facts.isFalse)
      constantFreedom
    else
      ccuDiseqConstantFreedom
//    ConstantFreedom.BOTTOM

  lazy val ccuFixedConstantFreedom : Boolean =
    constantFreedom == ccuClosingConstantFreedom

  lazy val mayAlias : ((LinearCombination, LinearCombination) => AliasStatus.Value) =
    new AliasAnalyser (reduceWithFacts,
                       constantFreedom, vocabulary.bindingContext,
                       order)
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * All constants that occur in formulas in this goal
   */
  lazy val constants : Set[ConstantTerm] =
    facts.constants ++ compoundFormulas.constants ++ tasks.taskInfos.constants
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Return whether <code>t</code> is a constant that is eliminated in this goal
   */
  def eliminates(t : Term) : Boolean = t match {
    case t : ConstantTerm => eliminatedConstants contains t
    case _ => false
  }

  lazy val reduceWithFacts : ReduceWithConjunction =
    ReduceWithConjunction(facts, Param.FUNCTIONAL_PREDICATES(settings),
                          Param.ASSUME_INFINITE_DOMAIN(settings),
                          order)
   
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
  def addTasksFor(fors : Iterable[Conjunction]) : Goal =
    if (facts.isFalse) {
      // new tasks are useless in this case; we have to be careful
      // not to delete the stored inferences
      this
    } else {
      val newTasks = for (f <- fors; t <- formulaTasks(f)) yield t
    
      val collector = getInferenceCollector
      if (collector.isLogging)
        for (f <- fors) collector newFormula f.negate

      Goal(facts, compoundFormulas, tasks ++ newTasks, age,
           eliminatedConstants, vocabulary, definedSyms, collector.getCollection,
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
      } else if (Param.CCU_SOLVER(settings).isDefined) {
        // if we are using CCU, just return the facts of this goal
        val factLits = (for (l <- facts.iterator) yield CertFormula(l)).toSet
        CCUCloseCertificate(factLits, order)
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
    "^ " + unifiabilityString /* closingConstraint */ + "\n" +
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
