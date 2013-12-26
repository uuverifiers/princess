/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import ap.terfor._
import ap.terfor.arithconj.{ArithConj, ReduceWithAC, ModelElement}
import ap.terfor.equations.EquationConj
import ap.terfor.preds.{PredConj, ReduceWithPredLits, Predicate}
import ap.terfor.substitutions.Substitution
import ap.util.{Debug, Logic, PlainRange, Timeout}


object ReduceWithConjunction {
  
  private val AC = Debug.AC_PROPAGATION

  def apply(conj : Conjunction, order : TermOrder) : ReduceWithConjunction =
    apply(conj, Set(), order)
  
  def apply(conj : Conjunction,
            functionalPreds : Set[Predicate],
            order : TermOrder) : ReduceWithConjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (conj isSortedBy order) &&
                    // conjunctions with quantifiers are not supported right now
                    conj.quans.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    new ReduceWithConjunction(ReduceWithAC(conj.arithConj, order),
                              ReduceWithPredLits(conj.predConj, functionalPreds, order),
                              order)
  }
  
  /**
   * Recursively reduce an arbitrary conjunction
   */
  private def reduceConj(conj : Conjunction,
                         initialReducer : ReduceWithConjunction,
                         logger : ComputationLogger) : Conjunction =
    if (conj.isTrue)
      conj
    else try {
      Timeout.check
      
      val (newArithConj, reducer) =
        if (conj.quans.size > 0)
          initialReducer.passQuantifiers(conj.quans.size)
                        .reduce(conj.arithConj, ComputationLogger.NonLogger)
        else
          initialReducer.reduce(conj.arithConj, logger)
    
      reducer.reduce(conj.predConj, logger) match {

        case Left((newPredConj, reducer2)) => {
          val newNegConjs = reduceNegatedConjs(conj.negatedConjs, reducer2)
          val res = constructConj(conj, conj.quans,
                                  newArithConj, newPredConj, newNegConjs,
                                  reducer2.order)    

          if ((conj.quans == res.quans) &&
              (newArithConj eq res.arithConj) &&
              (newPredConj eq res.predConj)) {
            res
          } else {
            // it might be necessary to repeat reduction, because new facts became
            // available
            reduceConj(res, initialReducer, logger)
          }
        }
        
        case Right((newPredConj, newEqs)) => {
          // the reduction has made some new equations available
          val newAC = ArithConj.conj(List(newArithConj, newEqs), reducer.order)
          if (newAC.isFalse) throw FALSE_EXCEPTION
          val newConj = Conjunction(conj.quans,
                                    newAC, newPredConj, conj.negatedConjs,
                                    reducer.order)
          reduceConj(newConj, initialReducer, logger)
        }
        
      }
          
    } catch {
      case FALSE_EXCEPTION => Conjunction.FALSE
    }

  private def reduceConj(conj : Conjunction,
                         initialReducer : ReduceWithConjunction) : Conjunction =
    reduceConj(conj, initialReducer, ComputationLogger.NonLogger)

  //////////////////////////////////////////////////////////////////////////////

  private def reduceNegatedConjs(conjs : NegatedConjunctions,
                                 reducer : ReduceWithConjunction)
                                : NegatedConjunctions = {
    var changed = false
    val newConjs = for (c <- conjs) yield {
      val reduced = reduceConj(c, reducer)
      if (reduced.isTrue)
        throw FALSE_EXCEPTION
      if (!(reduced eq c))
        changed = true
      reduced
    }

    if (changed)
      NegatedConjunctions(newConjs, reducer.order)
    else
      conjs
  }

  //////////////////////////////////////////////////////////////////////////////

  private def createConj(oldConj : Conjunction,
                         quans : Seq[Quantifier],
                         newArithConj : ArithConj,
                         newPredConj : PredConj,
                         newNegConjs : NegatedConjunctions,
                         order : TermOrder) : Conjunction =
    if (oldConj != null &&
        oldConj.quans == quans &&
        (oldConj.arithConj eq newArithConj) &&
        (oldConj.predConj eq newPredConj) &&
        (oldConj.negatedConjs eq newNegConjs))
      oldConj
    else
      Conjunction(quans, newArithConj, newPredConj, newNegConjs, order)

  private def constructConj(oldConj : Conjunction,
                            quans : Seq[Quantifier],
                            newArithConj : ArithConj,
                            newPredConj : PredConj,
                            newNegConjs : NegatedConjunctions,
                            order : TermOrder) : Conjunction =
    quans.headOption match {
      case Some(Quantifier.EX) => {
        var eliminableVars : Set[Term] = Set()
    
        var i : Int = 0
        while (i < quans.size && quans(i) == Quantifier.EX) {
          val variable = VariableTerm(i)
          if (!(newNegConjs.variables contains variable))
            eliminableVars = eliminableVars + variable
          i = i + 1
        }
    
        if (eliminableVars.isEmpty) {
          createConj(oldConj, quans, newArithConj, newPredConj, newNegConjs, order)
        } else {
          val literals =
            Conjunction(List(), newArithConj, newPredConj, NegatedConjunctions.TRUE, order)
          val eliminator =
            new LiteralEliminator(literals, eliminableVars, order)
          val essentialLits = 
            eliminator eliminate ComputationLogger.NonLogger
          
          val negConjs = if (eliminator.divJudgements.isEmpty)
              newNegConjs
            else
              NegatedConjunctions(newNegConjs ++ eliminator.divJudgements, order)

          val newConj =
            createConj(oldConj,
                       quans, essentialLits.arithConj, essentialLits.predConj,
                       negConjs, order)
          
          if (newConj.quans.headOption == Some(Quantifier.ALL))
            // iterate because it might be possible to eliminate further
            // quantifiers now
            constructConj(oldConj,
                          newConj.quans, newConj.arithConj, newConj.predConj,
                          newConj.negatedConjs, order)
          else
            newConj
        }
      }
      
      case Some(Quantifier.ALL)
        if (newArithConj.isLiteral && newPredConj.isTrue && newNegConjs.isTrue) => {

          // TODO: in which cases can this really work?

          val res =
            constructConj(null,
                          for (q <- quans) yield q.dual,
                          newArithConj.negate, PredConj.TRUE, NegatedConjunctions.TRUE,
                          order).negate
          if (oldConj != null && res == oldConj)
            oldConj
          else
            res
      }
      
      case Some(Quantifier.ALL)
        if (newArithConj.isTrue && newPredConj.isTrue && newNegConjs.size == 1) => {

          // TODO: in which cases can this really work?

          val subConj = newNegConjs(0)

          val res =
            constructConj(null,
                          subConj.quans ++ (for (q <- quans) yield q.dual),
                          subConj.arithConj, subConj.predConj, subConj.negatedConjs,
                          order).negate

          if (oldConj != null && res == oldConj)
            oldConj
          else
            res
      }
      
      case _ =>
        createConj(oldConj, quans, newArithConj, newPredConj, newNegConjs, order)
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Recursively reduce an arbitrary conjunction
   */
  private def reReduceConj(conj : Conjunction,
                           initialReducer : ReduceWithConjunction)
                          : Conjunction = try {
    val reducer = initialReducer.passQuantifiers(conj.quans.size)

    val newArithConj = reducer.plainReduce(conj.arithConj)

    if (newArithConj.isFalse)
      throw FALSE_EXCEPTION

    val (newPredConj, newEqs) = reducer plainReduce conj.predConj

    val newArithConj2 =
      if (newEqs.isTrue) {
        newArithConj
      } else {
        // the reduction has made some new equations available
        val newAC = ArithConj.conj(List(newArithConj, newEqs), reducer.order)
        if (newAC.isFalse) throw FALSE_EXCEPTION
        newAC
      }

    val newNegConjs = {
      var changed = false
      val newConjs = for (c <- conj.negatedConjs) yield {
        val reduced = reReduceConj(c, reducer)
        if (reduced.isTrue)
          throw FALSE_EXCEPTION
        if (!(reduced eq c))
          changed = true
        reduced
      }

      if (changed)
        NegatedConjunctions(newConjs, reducer.order)
      else
        conj.negatedConjs
    }

    if ((newArithConj2 eq conj.arithConj) &&
        (newPredConj eq conj.predConj) &&
        (newNegConjs eq conj.negatedConjs))
      conj
    else
      Conjunction(conj.quans, newArithConj2, newPredConj, newNegConjs,
                  reducer.order)
      
  } catch {
    case FALSE_EXCEPTION => Conjunction.FALSE
  }
  
}

class ReduceWithConjunction private (private val acReducer : ReduceWithAC,
                                     private val predReducer : ReduceWithPredLits,
                                     private val order : TermOrder) {

  def passQuantifiers(num : Int) : ReduceWithConjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, num >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (num == 0) {
      this
    } else {
      val new1 = acReducer passQuantifiers num
      val new2 = predReducer passQuantifiers num

      if ((new1 eq acReducer) && (new2 eq predReducer))
        this
      else
        new ReduceWithConjunction(new1, new2, order)
    }
  }

  /**
   * A reducer corresponding to this one, but without assuming
   * any facts known a priori.
   */
  lazy val withoutFacts =
    new ReduceWithConjunction(ReduceWithAC(ArithConj.TRUE, order),
                              predReducer.withoutFacts,
                              order)

  def addArithConj(ac : ArithConj) : ReduceWithConjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (ac.isEmpty)
      this
    else
      new ReduceWithConjunction(acReducer addArithConj ac, predReducer, order)
  }

  def apply(conj : Conjunction) : Conjunction =
    apply(conj, ComputationLogger.NonLogger)

  def apply(conj : Conjunction, logger : ComputationLogger) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
      
    val res = ReduceWithConjunction.reduceConj(conj, this, logger)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // we demand that the reducer is a projection (repeated application does not
    // change the result anymore)
    Debug.assertPostFast(ReduceWithConjunction.AC,
                         (ReduceWithConjunction.reduceConj(res, this) eq res) &&
                         ((res eq conj) || (res != conj)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Check whether <code>conj</code> can be simplified with the help
   * of assumed knowledge/facts. If yes, <code>conj</code> will be
   * fully reduced, otherwise <code>conj</code> will be returned unchanged.
   */
  def tentativeReduce(conj : Conjunction) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val simpConj = ReduceWithConjunction.reReduceConj(conj, this)
    val res = if (simpConj eq conj)
                conj
              else
                // if anything has changed, further internal
                // propagations might become available
                apply(simpConj)
/*
if (!(ReduceWithConjunction.reduceConj(res, this) eq res)) {
println(conj)
println("-> " + simpConj)
println("-> " + res)
println("-> " + ReduceWithConjunction.reduceConj(res, this))
}*/

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPostFast(ReduceWithConjunction.AC,
                         ((res eq conj) || (res != conj)) &&
                         // if the input had been reduced at some previous point,
                         // it is guaranteed to be fully reduced now
                         (!(withoutFacts(conj) eq conj) || (apply(res) eq res)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conjs : NegatedConjunctions) : NegatedConjunctions = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conjs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res = try {
      ReduceWithConjunction.reduceNegatedConjs(conjs, this)
    } catch {
      case FALSE_EXCEPTION => NegatedConjunctions.FALSE
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // we demand that the reducer is a projection (repeated application does not
    // change the result anymore)
    Debug.assertPostFast(ReduceWithConjunction.AC,
                         Logic.forall(for (c <- res.iterator) yield (this(c) eq c)) &&
                         ((res eq conjs) || (res != conjs)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : EquationConj) : EquationConj = acReducer(conj)
  def apply(conj : ArithConj) : ArithConj = acReducer(conj)
  
  private def replaceAC(newAC : ReduceWithAC) : ReduceWithConjunction =
    if (newAC eq this.acReducer)
      this
    else
      new ReduceWithConjunction(newAC, predReducer, order)
  
  private def replacePred(newPred : ReduceWithPredLits) : ReduceWithConjunction =
    if (newPred eq this.predReducer)
      this
    else
      new ReduceWithConjunction(acReducer, newPred, order)
  
  private def reduce(ac : ArithConj,
                     logger : ComputationLogger) : (ArithConj, ReduceWithConjunction) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (newArithConj, newACReducer) = acReducer.reduceAndAdd(ac, logger)
    if (newArithConj.isFalse) throw FALSE_EXCEPTION
    (newArithConj, this replaceAC newACReducer)
  }

  private def plainReduce(ac : ArithConj) : ArithConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    acReducer plainReduce ac
  }
  
  private def reduce(conj : PredConj, logger : ComputationLogger)
                    : Either[(PredConj, ReduceWithConjunction),
                             (PredConj, ArithConj)] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (conj.isTrue) {
      Left(conj, this)
    } else {
      val (redConj, newEqs) = predReducer(acReducer(conj, logger))
      if (redConj.isFalse) throw FALSE_EXCEPTION
      if (newEqs.isTrue)
        Left(redConj, this replacePred (predReducer addLits redConj))
      else
        Right(redConj, newEqs)
    }
  }
  
  private def plainReduce(conj : PredConj) : (PredConj, ArithConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (redConj, newEqs) =
      predReducer(acReducer(conj, ComputationLogger.NonLogger))
    if (redConj.isFalse) throw FALSE_EXCEPTION
    (redConj, newEqs)
  }
  
}

private object FALSE_EXCEPTION extends Exception

private class LiteralEliminator(literals : Conjunction,
                                uniVariables : Set[Term],
                                order : TermOrder)
              extends ConjunctEliminator(literals, uniVariables, Set(), order) {
  
  protected def nonUniversalElimination(f : Conjunction) =
    throw new UnsupportedOperationException
  
  protected def universalElimination(m : ModelElement) : Unit = {
    // nothing ... we do not need any witness information at this point
  }

  protected def addDivisibility(f : Conjunction) =
    divJudgements = f :: divJudgements

  var divJudgements : List[Conjunction] = List()

  protected def isEliminationCandidate(t : Term) : Boolean =
    uniVariables contains t

  protected def eliminationCandidates(literals : Conjunction) : Iterator[Term] =
    uniVariables.iterator
  
}
