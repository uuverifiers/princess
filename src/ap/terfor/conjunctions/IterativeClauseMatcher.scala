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

package ap.terfor.conjunctions

import ap.basetypes.IdealInt
import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.terfor.equations.{EquationConj, ReduceWithEqs}
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.Signature.{PredicateMatchStatus, PredicateMatchConfig}
import ap.util.{Debug, FilterIt, Seqs, UnionSet, Timeout}
import ap.PresburgerTools

import scala.collection.mutable.{ArrayBuffer, HashMap, LinkedHashMap,
                                 Map => MutableMap}
import scala.collection.{Set => GSet}

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
                             allLitFacts : PredConj,
                             isNotRedundant : (Conjunction, GSet[ConstantTerm]) => Boolean,
                             allowConditionalInstances : Boolean,
                             logger : ComputationLogger,
                             order : TermOrder) : Iterator[Conjunction] = {
    
    val selectedLits = new ArrayBuffer[Atom]
    
    val instances = new ArrayBuffer[Conjunction]

    var selectionCounter = 0
    
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * The recursive function for the actual matching.
     * The argument <code>conditional</code>
     * remembers whether a previous alias check has introduced some condition
     * that could only be discharged using the free-constant optimisation
     */
    def exec(program : List[MatchStatement],
             originatingConstants : GSet[ConstantTerm],
             conditional : Boolean) : Unit = {
          selectionCounter = selectionCounter + 1
          if (selectionCounter % 1000 == 0)
            Timeout.check

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
            exec(progTail,
                 UnionSet(originatingConstants, a.constants),
                 conditional)
          }
          for (a <- if (negative) additionalNegLits else additionalPosLits)
            if (a.pred == pred) {
              selectedLits(selLitsNum) = a
              exec(progTail,
                   UnionSet(originatingConstants, a.constants),
                   conditional)
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
            val allOriConstants =
              UnionSet(originatingConstants, originalClause.constants)

            val newAC = arithConj.updatePositiveEqs(newEqs)(order)
            val reducedInstance = 
              contextReducer(Conjunction(quans, newAC, remainingLits,
                                         negConjs, order))

            if (!reducedInstance.isFalse) {
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
  
                val instance =
                  ReduceWithConjunction(Conjunction.TRUE, order)(
                    originalClause.instantiate(instanceTerms)(order))

                if (isNotRedundant(instance, allOriConstants)) {
                  // check which of the literals of the instance can directly be
                  // discharged
                  val pc = instance.predConj
                  val (dischargedPosLits, remainingPosLits) =
                    pc.positiveLits partition allLitFacts.positiveLitsAsSet
                  val (dischargedNegLits, remainingNegLits) =
                    pc.negativeLits partition allLitFacts.negativeLitsAsSet

                  val dischargedLits =
                    pc.updateLitsSubset(dischargedPosLits, dischargedNegLits,
                                        order)
                  val simpInstance =
                    instance.updatePredConj(
                      pc.updateLitsSubset(remainingPosLits, remainingNegLits,
                                          order))(order)

                  logger.groundInstantiateQuantifier(originalClause.negate,
                                                     instanceTerms,
                                                     instance.negate,
                                                     dischargedLits,
                                                     simpInstance.negate, order)
                  instances += simpInstance
                }
                
              } else {
                if (isNotRedundant(reducedInstance, allOriConstants))
                  instances += reducedInstance
              }
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
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    selectedLits += startLit
    exec(program, startLit.constants, false)
    
    instances.iterator
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def constructMatcher(startPred : Predicate, negStartLit : Boolean,
                               clauses : Seq[Conjunction],
                               includeAxiomMatcher : Boolean)
                              (implicit config : PredicateMatchConfig) : List[MatchStatement] = {
    val matchers = new ArrayBuffer[List[MatchStatement]]
    
    if ((negStartLit && isNegativelyMatched(startPred)) ||
        (!negStartLit && isPositivelyMatched(startPred)))
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
                               clause : Conjunction)
                              (implicit config : PredicateMatchConfig)
                              : List[MatchStatement] = {
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
      res += SelectLiteral(a.pred, isNegativelyMatched(a.pred))
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
  private def determineMatchedLits(conj : PredConj)
                                  (implicit config : PredicateMatchConfig)
                                   : (Seq[Atom], PredConj) = {
    val (posMatched, posRemaining) =
      conj.positiveLits partition { a => isPositivelyMatched(a.pred) }
    val (negMatched, negRemaining) =
      conj.negativeLits partition { a => isNegativelyMatched(a.pred) }

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
  private def isPositivelyMatched(pred : Predicate)
                      (implicit config : PredicateMatchConfig) : Boolean =
    config.getOrElse(pred, PredicateMatchStatus.Positive) ==
      PredicateMatchStatus.Positive

  private def isNegativelyMatched(pred : Predicate)
                      (implicit config : PredicateMatchConfig) : Boolean =
    config.getOrElse(pred, PredicateMatchStatus.Positive) ==
      PredicateMatchStatus.Negative

  object Matchable extends Enumeration {
    val No, ProducesLits, Complete = Value
  }
  
  def isMatchable(c : Conjunction,
                  config : PredicateMatchConfig,
                  domainPredicates : Set[Predicate]) : Matchable.Value = {
    implicit val _config = config
    val (matchLits, remainingLits) = determineMatchedLits(c.predConj)
    if (matchLits.isEmpty)
      Matchable.No
    else if ((remainingLits.predicates subsetOf domainPredicates) &&
             (c.negatedConjs.predicates subsetOf domainPredicates))
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
  def isMatchableRec(c : Conjunction,
                     config : PredicateMatchConfig) : Boolean =
    isMatchableRecHelp(c, false, config)
  
  private def isMatchableRecHelp(c : Conjunction, negated : Boolean,
                                 config : PredicateMatchConfig) : Boolean = {
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
      (c.isQuantifiedDivisibility || c.isQuantifiedNonDivisibility)) || {
       // ... and all bound variables occur in matched predicate literals,
       // or can be eliminated through equations

       val matchedVariables = determineMatchedVariables(c, negated, config)
       (0 until lastUniQuantifier) forall (matchedVariables contains _)
     }) &&
    (c.negatedConjs forall (isMatchableRecHelp(_, !negated, config)))
  }

  private def determineMatchedVariables(
                  c : Conjunction, negated : Boolean,
                  config : PredicateMatchConfig) : Set[Int] =
    if (c.size == 1 && c.negatedConjs.size == 1) {
      determineMatchedVariables(c.negatedConjs.head, !negated, config)
    } else if (negated && !(c.size == 1 && c.predConj.isLiteral)) {
      Set()
    } else {
      implicit val _config = config
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
        
      (for (// Seq((IdealInt.ONE, VariableTerm(ind)), _*) <- quantVarEqs.iterator;
            lc <- quantVarEqs.iterator;
            if (!lc.isEmpty && lc.leadingCoeff.isOne &&
                lc.leadingTerm.isInstanceOf[VariableTerm]))
       yield lc.leadingTerm.asInstanceOf[VariableTerm].index).toSet
    }
  
  //////////////////////////////////////////////////////////////////////////////

  def convertQuantifiers(c : Conjunction, config : PredicateMatchConfig)
                        : Conjunction =
    convertQuantifiersHelp(c, false, config)

  private def convertQuantifiersHelp(c : Conjunction,
                                     negated : Boolean,
                                     config : PredicateMatchConfig)
                                    : Conjunction = {
    val ALL = Quantifier(negated)

    if (c.quans.isEmpty ||
        (!(c.quans.tail contains ALL) &&
         (c.quans.head != ALL ||
          c.isQuantifiedDivisibility || c.isQuantifiedNonDivisibility))) {

      val newNegConjs = c.negatedConjs.update(
                          for (d <- c.negatedConjs)
                          yield convertQuantifiersHelp(d, !negated, config),
                          c.order)
      c.updateNegatedConjs(newNegConjs)(c.order)

    } else if (c.predicates.isEmpty) {

      // just eliminate quantifiers; this is only correct
      // for integers (assuming infinite domains)
      PresburgerTools.elimQuantifiersWithPreds(c)

    } else {

      val EX = ALL.dual

      val newNegConjs = c.negatedConjs.update(
                          for (d <- c.negatedConjs)
                          yield convertQuantifiersHelp(d, !negated, config),
                          c.order)
      val newQuans = c.quans.toArray
      var changed = !(newNegConjs eq c.negatedConjs)

      def newC =
        if (changed)
          Conjunction.createFromNormalised(newQuans,
                                           c.arithConj, c.predConj, newNegConjs,
                                           c.order)
        else
          c

      val firstExQuantifier = (newQuans indexOf EX) match {
        case -1 => newQuans.size
        case x => x
      }

      // we know that newQuans contains ALL
      val lastUniQuantifier = (newQuans lastIndexOf ALL) + 1

      // the quantifier sequence has to be ALL* EX* ...
      for (i <- firstExQuantifier until lastUniQuantifier) {
        newQuans(i) = EX
        changed = true
      }

      val matchedVariables = determineMatchedVariables(c, negated, config)
      var contained = true
      for (i <- 0 until firstExQuantifier) {
        contained = contained && (matchedVariables contains i)
        if (!contained) {
          newQuans(i) = EX
          changed = true
        }
      }
      newC
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine the set of predicates that are matched in some
   * quantified expression
   */
  def matchedPredicatesRec(c : Conjunction,
                           config : PredicateMatchConfig) : Set[Predicate] =
    matchedPredicatesRecHelp(c, false, config)

  private def matchedPredicatesRecHelp(
                c : Conjunction,
                negated : Boolean,
                config : PredicateMatchConfig) : Set[Predicate] = {
    implicit val _config = config

    val subPreds =
      (for (d <- c.negatedConjs.iterator;
            p <- matchedPredicatesRecHelp(d, !negated, config).iterator)
       yield p).toSet

    val lastUniQuantifier = (c.quans lastIndexOf Quantifier(negated)) match {
      case -1 => 0
      case x => x + 1
    }

    if (!((c.quans take lastUniQuantifier) contains (Quantifier(!negated))) &&
        lastUniQuantifier > 0 &&
        !c.isQuantifiedDivisibility && !c.isQuantifiedNonDivisibility &&
        ((c.size == 1 && c.predConj.isLiteral) || !negated)) {
      val (matchLits, _) =
        determineMatchedLits(if (negated) c.predConj.negate else c.predConj)
      subPreds ++ (for (a <- matchLits.iterator) yield a.pred)
    } else {
      subPreds
    }
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
              : List[MatchStatement] = programs match {
    case Seq() => List()
    case Seq(prog) => prog
    case programs => {
      val res = new ArrayBuffer[List[MatchStatement]]

      // sort programs according to first SelectLiteral statement

      val selectLitProgs =
        new LinkedHashMap[SelectLiteral, ArrayBuffer[List[MatchStatement]]]
      var checkAliasProgs =
        new ArrayBuffer[List[MatchStatement]]
      val otherProgs =
        new ArrayBuffer[List[MatchStatement]]

      for (p <- programs) p match {
        case (stmt : SelectLiteral) :: _ =>
          selectLitProgs.getOrElseUpdate(stmt, new ArrayBuffer) += p
        case (_ : CheckMayAlias | _ : CheckMayAliasUnary) :: _ =>
          checkAliasProgs += p
        case _ =>
          otherProgs += p
      }

      for ((s, progs) <- selectLitProgs)
        if (progs.size == 1)
          res ++= progs
        else
          res += s :: combineMatchers(progs map (_.tail))

      // sort other programs according to the most frequent
      // CheckMayAlias statement

      val checkAliasNum = new LinkedHashMap[MatchStatement, Int]

      while (checkAliasProgs.size > 1) {
        for (p <- checkAliasProgs) {
          for (s <- p.iterator takeWhile {
                 case _ : CheckMayAlias | _ : CheckMayAliasUnary => true
                 case _ => false
               })
            checkAliasNum.put(s, checkAliasNum.getOrElse(s, 0) + 1)
        }

        val maxStmt = (checkAliasNum maxBy (_._2))._1
        checkAliasNum.clear

        val (selProgs, remProgs) = checkAliasProgs partition (_ contains maxStmt)
        checkAliasProgs = remProgs

        res += maxStmt :: combineMatchers(selProgs map (_ filterNot (_ == maxStmt)))
      }

      res ++= checkAliasProgs
      res ++= otherProgs

      res match {
        case Seq(prog) => prog
        case programs => List(Choice(programs))
      }
    }
  }

  def empty(matchAxioms : Boolean, config : PredicateMatchConfig) =
    IterativeClauseMatcher (PredConj.TRUE, NegatedConjunctions.TRUE,
                            matchAxioms,
                            Set(Conjunction.FALSE))(config)

  private def apply(currentFacts : PredConj,
                    currentClauses : NegatedConjunctions,
                    matchAxioms : Boolean,
                    generatedInstances : Set[Conjunction])
                   (implicit config : PredicateMatchConfig) =
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
                                     (implicit config : PredicateMatchConfig)
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
                  isIrrelevantMatch : (Conjunction, GSet[ConstantTerm]) => Boolean,
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
                         originatingConstants : GSet[ConstantTerm]) : Boolean =
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
                                                  newFacts,
                                                  isNotRedundant _,
                                                  allowConditionalInstances,
                                                  logger,
                                                  order)
        }

      (instances,
       new IterativeClauseMatcher(newFacts, clauses, matchAxioms, matchers,
                                  newGeneratedInstances))
    }

/*
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
*/

  def addClauses(addedClauses : Iterable[Conjunction],
                 mayAlias : (LinearCombination, LinearCombination) => AliasStatus.Value,
                 contextReducer : ReduceWithConjunction,
                 // predicate to distinguish the relevant matches
                 // (e.g., to filter out shielded formulae)
                 isIrrelevantMatch : (Conjunction, GSet[ConstantTerm]) => Boolean,
                 allowConditionalInstances : Boolean,
                 logger : ComputationLogger,
                 order : TermOrder) : (Iterable[Conjunction], IterativeClauseMatcher) =
    if (addedClauses.isEmpty) {
      (List(), this)
    } else {
      val newClauses =
        NegatedConjunctions(clauses.iterator ++ addedClauses.iterator, order)

      val tempMatcher =
        IterativeClauseMatcher(PredConj.TRUE,
                               NegatedConjunctions(addedClauses, order),
                               false, generatedInstances)
    
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
      val keptClauses = clauses.updateSubset(keptClausesSeq, clauses.order)
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
                   : (NegatedConjunctions, IterativeClauseMatcher) = {
    
    val keptClauses, reductions = new ArrayBuffer[Conjunction]
    for (c <- clauses) {
      val redC = reduceIfNecessary(c, clauseReducer)
      if (redC eq c)
        keptClauses += c
      else
        reductions += redC
    }
    
    // we also reduce the set of generated instances, because future
    // instantiations will be made modulo the new reducer
    var changedInstance = false
    val reducedInstances =
      for (i <- generatedInstances) yield {
        val newI = reduceIfNecessary(i, instanceReducer)
        if (!(newI eq i))
          changedInstance = true
        newI
      }
    
    (NegatedConjunctions(reductions, order),
     if (keptClauses.size == clauses.size && !changedInstance)
       // nothing has changed
       this
     else if (keptClauses.size == clauses.size)
       // just change the instance cache
       new IterativeClauseMatcher(currentFacts, clauses, matchAxioms,
                                  matchers, reducedInstances)
     else
       // reset the matchers
       IterativeClauseMatcher(currentFacts, clauses.updateSubset(keptClauses, order),
                              matchAxioms, reducedInstances))
  }

  private def reduceIfNecessary(conj : Conjunction,
                                reducer : (Conjunction) => Conjunction) : Conjunction =
    if (conj.constants.isEmpty && conj.predicates.isEmpty) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // The assumption is that clauses without constants or ground atoms
      // are already fully reduced
      Debug.assertInt(IterativeClauseMatcher.AC, reducer(conj) eq conj)
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

  def isEmpty : Boolean = clauses.isEmpty
  
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
