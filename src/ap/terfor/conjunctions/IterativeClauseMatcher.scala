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

package ap.terfor.conjunctions

import ap.basetypes.IdealInt
import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, ReduceWithEqs}
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.util.{Debug, FilterIt, Seqs}

import scala.collection.mutable.{ArrayBuffer, HashMap}
import scala.collection.mutable.{Map => MutableMap}

object IterativeClauseMatcher {
  
  private val AC = Debug.AC_CLAUSE_MATCHER
  
  private def executeMatcher(startLit : Atom,
                             negatedStartLit : Boolean,
                             program : List[MatchStatement],
                             litFacts : PredConj,
                             additionalPosLits : Iterable[Atom],
                             additionalNegLits : Iterable[Atom],
                             mayAlias : (LinearCombination,
                                         LinearCombination) => AliasStatus.Value,
                             contextReducer : ReduceWithConjunction,
                             isNotRedundant : (Conjunction, Set[ConstantTerm]) => Boolean,
                             allowConditionalInstances : Boolean,
                             logger : ComputationLogger,
                             order : TermOrder) : Iterator[Conjunction] = {
    
    val selectedLits = new ArrayBuffer[Atom]
    
    val instances = new ArrayBuffer[Conjunction]

    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * The recursive function for the actual matching.
     * The argument <code>conditional</code>
     * remembers whether a previous alias check has introduced some condition
     * that could only be discharged using the free-constant optimisation
     */
    def exec(program : List[MatchStatement],
             originatingConstants : Set[ConstantTerm],
             conditional : Boolean) : Unit =
      program match {
        
        case List() => // nothing
          
        case SelectLiteral(pred, negative) :: progTail => {
          val selLitsNum = selectedLits.size
          selectedLits += null
          
          val atoms = if (negative)
                        litFacts negativeLitsWithPred pred
                      else
                        litFacts positiveLitsWithPred pred
          
          for (a <- atoms) {
            selectedLits(selLitsNum) = a
            exec(progTail, originatingConstants ++ a.constants, conditional)
          }
          for (a <- if (negative) additionalNegLits else additionalPosLits)
            if (a.pred == pred) {
              selectedLits(selLitsNum) = a
              exec(progTail, originatingConstants ++ a.constants, conditional)
            }
          
          selectedLits reduceToSize selLitsNum
        }
        
        case CheckMayAlias(litNrA, argNrA, litNrB, argNrB) :: progTail =>
          mayAlias(selectedLits(litNrA)(argNrA), selectedLits(litNrB)(argNrB)) match {
            case AliasStatus.Must | AliasStatus.May =>
              exec(progTail, originatingConstants, conditional)
            case AliasStatus.CannotDueToFreedom
                if (allowConditionalInstances && !conditional) =>
              exec(progTail, originatingConstants, true)
            case _ =>
              // nothing
          }
        
        case CheckMayAliasUnary(litNr, argNr, lc) :: progTail =>
          mayAlias(selectedLits(litNr)(argNr), lc) match {
            case AliasStatus.Must | AliasStatus.May =>
              exec(progTail, originatingConstants, conditional)
            case AliasStatus.CannotDueToFreedom
                if (allowConditionalInstances && !conditional) =>
              exec(progTail, originatingConstants, true)
            case _ =>
              // nothing
          }

        case InstantiateClause(originalClause, matchedLits, quans, arithConj,
                               remainingLits, negConjs) :: progTail => {
          // we generate a system of equations that precisely describes the
          // match conditions
          
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(IterativeClauseMatcher.AC, matchedLits.size == selectedLits.size)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          
          val newEqs = EquationConj(
            (for ((a1, a2) <- (matchedLits.iterator zip selectedLits.iterator);
                  lc <- a1.unificationConditions(a2, order))
             yield lc) ++
            arithConj.positiveEqs.iterator,
            order)
          
          if (!newEqs.isFalse) {
            val allOriConstants = originatingConstants ++ originalClause.constants
            if (logger.isLogging) {
              // If we are logging, we avoid simplifications (which would not
              // be captured in the proof) and rather just substitute terms for
              // the quantified variables. Hopefully this is possible ...
              
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              // Currently, we just assume that all leading quantifiers are
              // existential (is the other case possible at all?)
              Debug.assertInt(IterativeClauseMatcher.AC,
                              quans forall (Quantifier.EX == _))
              //-END-ASSERTION-/////////////////////////////////////////////////
              
              val reducer = ReduceWithEqs(newEqs, order)
              val instanceTerms =
                (for (i <- 0 until quans.size)
                 yield reducer(LinearCombination(VariableTerm(i), order))).toList

              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(IterativeClauseMatcher.AC,
                              instanceTerms forall (_.variables.isEmpty))
              //-END-ASSERTION-/////////////////////////////////////////////////

              val instance = originalClause.instantiate(instanceTerms)(order)
              if (isNotRedundant(contextReducer(instance), allOriConstants)) {
                logger.groundInstantiateQuantifier(originalClause.negate,
                                                   instanceTerms, instance.negate, order)
                instances += instance
              }
              
            } else {
              val newAC = arithConj.updatePositiveEqs(newEqs)(order)
              val reducedInstance = 
                contextReducer(Conjunction(quans, newAC, remainingLits,
                                           negConjs, order))
              if (isNotRedundant(reducedInstance, allOriConstants))
                instances += reducedInstance
            }
          }
          
          exec(progTail, originatingConstants, conditional)
        }
        
        case UnifyLiterals(litNrA, litNrB) :: progTail => {
          val eqs = selectedLits(litNrA).unify(selectedLits(litNrB), order)
          if (!eqs.isFalse) {
            if (logger.isLogging) {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              // We currently only support the case that the first unified
              // literal is the start literal
              // (otherwise, we would have to store more information about
              // polarity of unified predicates)
              Debug.assertInt(AC, litNrA == 0 && litNrB == 1)
              //-END-ASSERTION-/////////////////////////////////////////////////
              val (leftNr, rightNr) =
                if (negatedStartLit) (litNrB, litNrA) else (litNrA, litNrB)
              
              val instance = Conjunction.conj(eqs, order)
              if (isNotRedundant(contextReducer(instance), originatingConstants)) {
                logger.unifyPredicates(selectedLits(leftNr), selectedLits(rightNr),
                                       eqs, order)
                instances += instance
              }
            } else {
              val reducedInstance = contextReducer(Conjunction.conj(eqs, order))
              if (isNotRedundant(reducedInstance, originatingConstants))
            	instances += reducedInstance
            }
          }
        }
        
        case Choice(options) :: progTail => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // Choice always has to be the last statement in a program
          Debug.assertInt(IterativeClauseMatcher.AC, progTail.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          
          for (prog <- options)
            exec(prog, originatingConstants, conditional)
        }
      }
    
    ////////////////////////////////////////////////////////////////////////////
    
    selectedLits += startLit
    exec(program, startLit.constants, false)
    
    instances.iterator
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def constructMatcher(startPred : Predicate, negStartLit : Boolean,
                               clauses : Seq[Conjunction],
                               includeAxiomMatcher : Boolean) : List[MatchStatement] = {
    val matchers = new ArrayBuffer[List[MatchStatement]]
    
    if (isPositivelyMatched(startPred) != negStartLit)
      for (clause <- clauses) {
        val startLits = if (negStartLit)
                          clause.predConj.negativeLitsWithPred(startPred)
                        else
                          clause.predConj.positiveLitsWithPred(startPred)
        for (startLit <- startLits)
          matchers += constructMatcher(startLit, negStartLit, clause)
      }
    
    if (includeAxiomMatcher)
      matchers += constructAxiomMatcher(startPred, negStartLit)
    
    combineMatchers(matchers)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Construct a matcher program for the given clause and the given start
   * literal
   */
  private def constructMatcher(startLit : Atom, negStartLit : Boolean,
                               clause : Conjunction) : List[MatchStatement] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC,
                    ((if (negStartLit)
                       clause.predConj.negativeLitsAsSet
                     else
                       clause.predConj.positiveLitsAsSet) contains startLit) &&
                    (clause.quans forall (Quantifier.EX ==)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val (matchedLits, remainingLits) = determineMatchedLits(clause.predConj)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, matchedLits contains startLit)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val nonStartMatchedLits = matchedLits filter (startLit !=)
    
    val res = new ArrayBuffer[MatchStatement]
    val knownTerms = new HashMap[LinearCombination, ArrayBuffer[(Int, Int)]]

    def genAliasChecks(a : Atom, litNr : Int) : Unit =
      for ((lc, argNr) <- a.iterator.zipWithIndex) {
        for ((oldLitNr, oldArgNr) <- knownTerms.getOrElseUpdate(lc, new ArrayBuffer))
          res += CheckMayAlias(oldLitNr, oldArgNr, litNr, argNr)
        if (lc.variables.isEmpty)
          res += CheckMayAliasUnary(litNr, argNr, lc)
        knownTerms.getOrElseUpdate(lc, new ArrayBuffer) += (litNr -> argNr)
      }

    genAliasChecks(startLit, 0)
    
    for ((a, litNr) <- nonStartMatchedLits.iterator.zipWithIndex) {
      res += SelectLiteral(a.pred, !isPositivelyMatched(a))
      genAliasChecks(a, litNr + 1)
    }
    
    res += InstantiateClause(clause, Seq(startLit) ++ nonStartMatchedLits,
                             clause.quans, clause.arithConj,
                             remainingLits, clause.negatedConjs)
    
    res.toList
  }
  
  /**
   * Given a conjunction of atoms, determine which atoms are to be matched on
   * facts. The 2nd component of the result are the remaining literals.
   */
  private def determineMatchedLits(conj : PredConj) : (Seq[Atom], PredConj) = {
    val (posMatched, posRemaining) =
      conj.positiveLits partition (isPositivelyMatched(_))
    val (negMatched, negRemaining) =
      conj.negativeLits partition (!isPositivelyMatched(_))

    (posMatched ++ negMatched,
     conj.updateLitsSubset(posRemaining, negRemaining, conj.order))
  }

  /**
   * For a certain atom, determine whether the positive occurrences or the
   * negative occurrences are to be resolved.
   *
   * TODO: generalise this so that for some predicates the positive occurrences,
   * for some predicates the negative occurrences are resolved
   */
  private def isPositivelyMatched(a : Atom) : Boolean = true
  private def isPositivelyMatched(pred : Predicate) : Boolean = true

  object Matchable extends Enumeration {
    val No, ProducesLits, Complete = Value
  }
  
  def isMatchable(c : Conjunction) : Matchable.Value = {
    val (matchLits, remainingLits) = determineMatchedLits(c.predConj)
    if (matchLits.isEmpty)
      Matchable.No
    else if (remainingLits.isTrue && c.negatedConjs.predicates.isEmpty)
      Matchable.Complete
    else
      Matchable.ProducesLits
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine whether all quantifiers in the given formula can be handled
   * using matching or using Skolemisation. This is relevant, because then
   * the formula can be treated without using free variables at all, i.e.,
   * a more efficient way of proof construction (<code>ModelSearchProver</code>)
   * can be used
   */
  def isMatchableRec(c : Conjunction) : Boolean =
    isMatchableRecHelp(c, false)
  
  private def isMatchableRecHelp(c : Conjunction, negated : Boolean) : Boolean = {
    val lastUniQuantifier = (c.quans lastIndexOf Quantifier(negated)) match {
      case -1 => 0
      case x => x + 1
    }
    
    // the quantifier sequence has to be ALL* EX* ...
    !((c.quans take lastUniQuantifier) contains (Quantifier(!negated))) &&
    // ... the expression underneath the quantifiers has to be a literal
    // or a disjunction ...
    (lastUniQuantifier == 0 ||
     (lastUniQuantifier == 1 &&
      (c.isQuantifiedDivisibility || c.isQuantifiedNonDivisibility)) ||
     ((c.size == 1 && c.predConj.isLiteral) || !negated) && {
       // ... and all bound variables occur in matched predicate literals,
       // or can be eliminated through equations
       implicit val order = c.order
       val reducedPreds =
         ReduceWithEqs(c.arithConj.positiveEqs, order)(c.predConj)
       val (matchLits, _) =
         determineMatchedLits(if (negated) reducedPreds.negate else reducedPreds)

       val eqs = c.arithConj.positiveEqs
         
       // figure out which variables are actually uniquely determined by
       // the matching
       val maxVarIndex =
         Seqs.max(for (a <- matchLits.iterator;
                       v <- a.variables.iterator) yield v.index) max
         Seqs.max(for (v <- eqs.variables.iterator) yield v.index)

       // set up the equations that determine the values of variables
       var i = maxVarIndex + 1
       val quantVarEqs = EquationConj(
             eqs.iterator ++
             (for (a <- matchLits.iterator; lc <- a.iterator) yield {
                val res = lc - LinearCombination(VariableTerm(i), order)
                i = i + 1
                res
              }),
           c.order)
         
       val matchedVariables =
         (for (// Seq((IdealInt.ONE, VariableTerm(ind)), _*) <- quantVarEqs.iterator;
               lc <- quantVarEqs.iterator;
               if (!lc.isEmpty && lc.leadingCoeff.isOne &&
                   lc.leadingTerm.isInstanceOf[VariableTerm]))
          yield lc.leadingTerm.asInstanceOf[VariableTerm].index).toSet
       (0 until lastUniQuantifier) forall (matchedVariables contains _)
     }) &&
    (c.negatedConjs forall (isMatchableRecHelp(_, !negated)))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def constructAxiomMatcher(pred : Predicate,
                                    negStartLit : Boolean) : List[MatchStatement] = {
    val res = new ArrayBuffer[MatchStatement]

    res += SelectLiteral(pred, !negStartLit)
    for (i <- 0 until pred.arity)
      res += CheckMayAlias(0, i, 1, i)
    
    res += UnifyLiterals(0, 1)
    
    res.toList
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private def combineMatchers(programs : Seq[List[MatchStatement]])
              : List[MatchStatement] =
    // TODO: more efficient implementation
    List(Choice(programs))

  def empty(matchAxioms : Boolean) =
    IterativeClauseMatcher (PredConj.TRUE, NegatedConjunctions.TRUE,
                            matchAxioms,
                            Set(Conjunction.FALSE))

  private def apply(currentFacts : PredConj,
                    currentClauses : NegatedConjunctions,
                    matchAxioms : Boolean,
                    generatedInstances : Set[Conjunction]) =
    new IterativeClauseMatcher(currentFacts, currentClauses, matchAxioms,
                               new HashMap[(Predicate, Boolean), List[MatchStatement]],
                               generatedInstances)
  
}

////////////////////////////////////////////////////////////////////////////////

class IterativeClauseMatcher private (currentFacts : PredConj,
                                      val clauses : NegatedConjunctions,
                                      matchAxioms : Boolean,
                                      matchers : MutableMap[(Predicate, Boolean),
                                                            List[MatchStatement]],
                                      // All instances that have already been
                                      // generated by this match. This is used
                                      // to prevent redundant instantiation
                                      generatedInstances : Set[Conjunction])
      extends Sorted[IterativeClauseMatcher] {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IterativeClauseMatcher.AC,
                   (clauses forall ((c) =>
                        (c.quans forall (Quantifier.EX ==)) &&
                        !(IterativeClauseMatcher
                              .determineMatchedLits(c.predConj) _1).isEmpty)) &&
                   // we assume that FALSE always exists as a generated
                   // instance, because we don't want to generate it at all
                   (generatedInstances contains Conjunction.FALSE))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  private def matcherFor(pred : Predicate, negated : Boolean) : List[MatchStatement] =
    matchers.getOrElseUpdate(
      (pred, negated),
      IterativeClauseMatcher.constructMatcher(pred, negated, clauses, matchAxioms))
  
  def updateFacts(newFacts : PredConj,
                  mayAlias : (LinearCombination, LinearCombination) => AliasStatus.Value,
                  contextReducer : ReduceWithConjunction,
                  // predicate to distinguish the relevant matches
                  // (e.g., to filter out shielded formulae)
                  isIrrelevantMatch : (Conjunction, Set[ConstantTerm]) => Boolean,
                  allowConditionalInstances : Boolean,
                  logger : ComputationLogger,
                  order : TermOrder) : (Iterable[Conjunction], IterativeClauseMatcher) =
    if (currentFacts == newFacts) {
      (List(), this)
    } else {
      val (oldFacts, addedFacts) = newFacts diff currentFacts
    
      val instances = new scala.collection.mutable.LinkedHashSet[Conjunction]
      val additionalPosLits, additionalNegLits = new ArrayBuffer[Atom]
      
      var newGeneratedInstances = generatedInstances
      def isNotRedundant(reducedInstance : Conjunction,
                         originatingConstants : Set[ConstantTerm]) : Boolean =
        if ((newGeneratedInstances contains reducedInstance) ||
            isIrrelevantMatch(reducedInstance, originatingConstants)) {
          false
        } else {
          newGeneratedInstances = newGeneratedInstances + reducedInstance
          true
        }
      
      for (negated <- List(false, true))
        for (a <- if (negated) addedFacts.negativeLits else addedFacts.positiveLits) {
          (if (negated) additionalNegLits else additionalPosLits) += a
          
          instances ++=
            IterativeClauseMatcher.executeMatcher(a,
                                                  negated,
                                                  matcherFor(a.pred, negated),
                                                  oldFacts,
                                                  additionalPosLits, additionalNegLits,
                                                  mayAlias,
                                                  contextReducer,
                                                  isNotRedundant _,
                                                  allowConditionalInstances,
                                                  logger,
                                                  order)
        }

      (instances,
       new IterativeClauseMatcher(newFacts, clauses, matchAxioms, matchers,
                                  newGeneratedInstances))
    }

  def updateClauses(newClauses : NegatedConjunctions,
                    mayAlias : (LinearCombination, LinearCombination) => AliasStatus.Value,
                    contextReducer : ReduceWithConjunction,
                    // predicate to distinguish the relevant matches
                    // (e.g., to filter out shielded formulae)
                    isIrrelevantMatch : (Conjunction, Set[ConstantTerm]) => Boolean,
                    allowConditionalInstances : Boolean,
                    logger : ComputationLogger,
                    order : TermOrder) : (Iterable[Conjunction], IterativeClauseMatcher) =
    if (clauses == newClauses) {
      (List(), this)
    } else {
      val (oldClauses, addedClauses) = newClauses diff clauses
      val tempMatcher =
        IterativeClauseMatcher(PredConj.TRUE, addedClauses, false, generatedInstances)
    
      val (instances, _) =
        tempMatcher.updateFacts(currentFacts,
                                mayAlias, contextReducer, isIrrelevantMatch,
                                allowConditionalInstances, logger, order)
    
      (instances,
       IterativeClauseMatcher(currentFacts, newClauses, matchAxioms,
                              generatedInstances ++ instances))
    }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Remove clauses and cached literals from this matcher that are identified
   * by the given predicate. The removed clauses are returned as the first
   * result component.
   */
  def remove(removePred : (Formula) => Boolean)
             : (Seq[Conjunction], IterativeClauseMatcher) = {
    val (removedClauses, keptClausesSeq) = clauses partition removePred
    val (removedLits, keptLits) = currentFacts partition removePred
    
    if (removedClauses.isEmpty) {
      if (removedLits.isTrue)
        (List(), this)
      else
        (List(),
         new IterativeClauseMatcher(keptLits, clauses, matchAxioms, matchers,
                                    generatedInstances))
    } else {
      val keptClauses = clauses.update(keptClausesSeq, clauses.order)
      (removedClauses,
       new IterativeClauseMatcher(keptLits, keptClauses, matchAxioms, matchers,
                                  generatedInstances))
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Reduce the clauses of this matcher. All reducible clauses are removed from
   * the matcher and the reductions are returned
   */
  def reduceClauses(clauseReducer : (Conjunction) => Conjunction,
                    instanceReducer : (Conjunction) => Conjunction,
                    order : TermOrder)
                   : (Seq[Conjunction], IterativeClauseMatcher) = {
    val reducedClauses =
      clauses.update(for (c <- clauses) yield reduceIfNecessary(c, clauseReducer),
                     order)

    val (keptClauses, reductions) = reducedClauses diff clauses
    
    // we also reduce the set of generated instances, because future
    // instantiations will be made modulo the new reducer
    val reducedInstances =
      for (i <- generatedInstances) yield reduceIfNecessary(i, instanceReducer)
    
    (reductions,
     if (keptClauses.size == clauses.size && generatedInstances == reducedInstances)
       // nothing has changed
       this
     else
       // reset the matchers
       IterativeClauseMatcher(currentFacts, keptClauses, matchAxioms, reducedInstances))
  }

  private def reduceIfNecessary(conj : Conjunction,
                                reducer : (Conjunction) => Conjunction) : Conjunction =
    if (conj.constants.isEmpty && conj.groundAtoms.isEmpty) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // The assumption is that clauses without constants or ground atoms
      // are already fully reduced
      Debug.assertInt(IterativeClauseMatcher.AC, reducer(conj) == conj)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      conj
    } else {
      reducer(conj)
    }

  //////////////////////////////////////////////////////////////////////////////
  
  def sortBy(order : TermOrder) : IterativeClauseMatcher =
    if (this isSortedBy order)
      this
    else
      IterativeClauseMatcher(currentFacts sortBy order,
                             clauses sortBy order,
                             matchAxioms,
                             for (i <- generatedInstances) yield (i sortBy order))
  
  def isSortedBy(order : TermOrder) : Boolean =
    (currentFacts isSortedBy order) && (clauses isSortedBy order)
  
  override def toString : String =
    "(" + this.currentFacts + ", " + this.clauses + ")"
  
  /**
   * Only used for assertion purposes
   */
  def factsAreOutdated(actualFacts : PredConj) : Boolean =
    !(actualFacts.positiveLitsAsSet subsetOf currentFacts.positiveLitsAsSet) ||
    !(actualFacts.negativeLitsAsSet subsetOf currentFacts.negativeLitsAsSet)
}

////////////////////////////////////////////////////////////////////////////////
// AST for programs that match certain literals in clauses on facts
//
// Such programs can pick predicate literals with certain predicates and
// polarities and check the may-alias relation for the arguments of such
// predicates. Each program starts with an implicitly selected literal (the
// start-literal)

private abstract sealed class MatchStatement

private case class SelectLiteral(pred : Predicate, negative : Boolean)
                   extends MatchStatement

private case class CheckMayAlias(litNrA : Int, argNrA : Int,
                                 litNrB : Int, argNrB : Int)
                   extends MatchStatement

private case class CheckMayAliasUnary(litNr : Int, argNr : Int,
                                      lc : LinearCombination)
                   extends MatchStatement

private case class InstantiateClause(originalClause : Conjunction,
                                     matchedLits : Seq[Atom],
                                     quans : Seq[Quantifier],
                                     arithConj : ArithConj,
                                     remainingLits : PredConj,
                                     negConjs : NegatedConjunctions)
                   extends MatchStatement

private case class UnifyLiterals(litNrA : Int, litNrB : Int)
                   extends MatchStatement
                   
private case class Choice(options : Seq[List[MatchStatement]])
                   extends MatchStatement
