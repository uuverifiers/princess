/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import ap.basetypes.IdealInt
import ap.terfor._
import ap.terfor.arithconj.{ArithConj, ReduceWithAC, ModelElement}
import ap.terfor.equations.EquationConj
import ap.terfor.preds.{PredConj, ReduceWithPredLits, Predicate}
import ap.terfor.substitutions.Substitution
import ap.parameters.{ReducerSettings, Param}
import ap.util.{Debug, Logic, PlainRange, Timeout}


object ReduceWithConjunction {
  
  private val AC = Debug.AC_PROPAGATION

  def apply(conj : Conjunction,
            order : TermOrder,
            settings : ReducerSettings = ReducerSettings.DEFAULT)
           : ReduceWithConjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (conj.quans.isEmpty)
      new ReduceWithConjunction(ReduceWithAC(conj.arithConj, order),
                                ReduceWithPredLits(
                                  conj.predConj,
                                  Param.FUNCTIONAL_PREDICATES(settings),
                                  order),
                                Param.REDUCER_PLUGIN(settings)(conj, order),
                                order)
    else
      // formulas with quantifiers are not supported right now
      apply(Conjunction.TRUE, order, settings)
  }
  
  /**
   * Recursively reduce an arbitrary conjunction
   */
  private def reduceConj(conj : Conjunction,
                         initialReducer : ReduceWithConjunction,
                         logger : ComputationLogger) : Conjunction =
    if (conj.isTrue) {
      conj
    } else try {
      Timeout.check

      implicit val order = initialReducer.order
      var currentArithConj = conj.arithConj
      var currentPredConj = conj.predConj
      var currentNegConjs = conj.negatedConjs
      
      val innerReducer = initialReducer passQuantifiers conj.quans.size

      // outer loop, reducing both arithmetic and predicate constraints
      while(true) {
        val (newArithConj, reducerWithAC) =
          innerReducer.reduce(currentArithConj, logger)
        currentArithConj = newArithConj

        // inner loop, reducing only predicate constraints
        var contInner = true
        while (contInner) reducerWithAC.reduce(currentPredConj, logger) match {

          case Left((newPredConj, reducerWithPC)) => {
            currentPredConj = newPredConj
            reducerWithPC.reduceWithPlugin(
                              currentPredConj, logger,
                              ReducerPlugin.ReductionMode.Contextual) match {

              case Left(reducerWithPC2) => {
                // reducer plugin converged

                currentNegConjs =
                  reduceNegatedConjs(currentNegConjs, reducerWithPC2)
                val preRes = constructConj(conj, conj.quans,
                                           currentArithConj,
                                           currentPredConj,
                                           currentNegConjs,
                                           order)
                val res = initialReducer.reducerPlugin finalReduce preRes
    
                if ((conj.quans == res.quans) &&
                    (currentArithConj eq res.arithConj) &&
                    (currentPredConj eq res.predConj)) {
                  return res
                } else {
                  // it might be necessary to repeat reduction, because new
                  // facts became available
                  return reduceConj(res, initialReducer, logger)
                }
              }

              case Right(ReducerPlugin.ChangedConjResult(addArithConj,
                                                         newPredConj,
                                                         addNegConjs)) => {
                currentPredConj = newPredConj
                currentNegConjs = currentNegConjs & addNegConjs

                if (addArithConj.isTrue) {
                  // continue in the inner loop
                } else {
                  currentArithConj =
                    ArithConj.conj(List(currentArithConj, addArithConj), order)
                  if (currentArithConj.isFalse) throw FALSE_EXCEPTION
                  contInner = false
                }
              }

            }
          }

          case Right((newPredConj, newEqs)) => {
            // the reduction has made some new equations available, continue
            // in the outer loop

            currentPredConj = newPredConj
            currentArithConj = ArithConj.conj(List(currentArithConj, newEqs),
                                              order)
            if (currentArithConj.isFalse) throw FALSE_EXCEPTION

            contInner = false
          }

        }
      }

      null // unreachable

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
    
        val quansSize = quans.size
        var i : Int = 0
        while (i < quansSize && quans(i) == Quantifier.EX) {
          val variable = VariableTerm(i)
          if (!(newNegConjs.variables contains variable))
            eliminableVars = eliminableVars + variable
          i = i + 1
        }
    
        if (eliminableVars.isEmpty) {
          createConj(oldConj, quans, newArithConj, newPredConj, newNegConjs,
                     order)
        } else {
          val literals =
            Conjunction(List(), newArithConj, newPredConj,
                        NegatedConjunctions.TRUE, order)
          val eliminator =
            new LiteralEliminator(literals, eliminableVars, order)
          val essentialLits = 
            eliminator eliminate ComputationLogger.NonLogger
          
          val negConjs =
            if (eliminator.divJudgements.isEmpty)
              newNegConjs
            else
              NegatedConjunctions(newNegConjs ++ eliminator.divJudgements,
                                  order)

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
    val reducer = initialReducer passQuantifiers conj.quans.size
    val (newArithConj, reducer2) = reducer plainReduce conj.arithConj

    if (newArithConj.isFalse)
      throw FALSE_EXCEPTION
    if (!(newArithConj eq conj.arithConj))
      return conj.updateArithConj(newArithConj)(reducer2.order)

    val (newPredConj, newEqs) = reducer2 plainReduce conj.predConj

    val newArithConj2 =
      if (newEqs.isTrue) {
        newArithConj
      } else {
        // the reduction has made some new equations available
        val newAC = ArithConj.conj(List(newArithConj, newEqs), reducer2.order)
        if (newAC.isFalse) throw FALSE_EXCEPTION
        newAC
      }

    if (!(newArithConj2 eq conj.arithConj) || !(newPredConj eq conj.predConj))
      return Conjunction(conj.quans, newArithConj2, newPredConj,
                         conj.negatedConjs, reducer2.order)

    reducer2.reduceWithPlugin(newPredConj, ComputationLogger.NonLogger,
                              ReducerPlugin.ReductionMode.Simple) match {
      case Left(reducer3) => {
        var changed = false
          
        val newConjs = for (c <- conj.negatedConjs) yield {
          if (changed) {
            // then we will do a second, contextual reduction pass anyway
            c
          } else {
            val reduced = reReduceConj(c, reducer3)
            if (reduced.isTrue)
              throw FALSE_EXCEPTION
            if (!(reduced eq c))
              changed = true
            reduced
          }
        }
    
        if (changed) {
          val newNegConjs = NegatedConjunctions(newConjs, reducer3.order)
          Conjunction(conj.quans, newArithConj2, newPredConj, newNegConjs,
                      reducer3.order)
        } else {
          conj
        }
      }

      case Right(ReducerPlugin.ChangedConjResult(addArithConj,
                                                 newPredConj2,
                                                 addNegConjs)) => {
        val newArithConj3 =
          ArithConj.conj(List(newArithConj2, addArithConj), reducer2.order)
        val newNegConjs =
          (conj.negatedConjs & addNegConjs)(reducer2.order)
        Conjunction(conj.quans, newArithConj3, newPredConj2, newNegConjs,
                    reducer2.order)
      }
    }

  } catch {
    case FALSE_EXCEPTION => Conjunction.FALSE
  }
  
}

class ReduceWithConjunction private (private val acReducer : ReduceWithAC,
                                     private val predReducer : ReduceWithPredLits,
                                     private val reducerPlugin : ReducerPlugin,
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
      val new3 = reducerPlugin passQuantifiers num

      if ((new1 eq acReducer) &&
          (new2 eq predReducer) &&
          (new3 eq reducerPlugin))
        this
      else
        new ReduceWithConjunction(new1, new2, new3, order)
    }
  }

  /**
   * A reducer corresponding to this one, but without assuming
   * any facts known a priori.
   */
  lazy val withoutFacts =
    new ReduceWithConjunction(ReduceWithAC(ArithConj.TRUE, order),
                              predReducer.withoutFacts,
                              reducerPlugin.factory(Conjunction.TRUE, order),
                              order)


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
               (ReduceWithConjunction.reduceConj(res, this, logger) eq res) &&
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

  /**
   * Check whether known inequalities imply a lower bound of the given term.
   */
  def lowerBound(t : Term) : Option[IdealInt] = acReducer lowerBound t

  /**
   * Check whether known inequalities imply an upper bound of the given
   * term.
   */
  def upperBound(t : Term) : Option[IdealInt] = acReducer upperBound t

  private def replace(newAC : ReduceWithAC,
                      newPlugin : ReducerPlugin) : ReduceWithConjunction =
    if ((newAC eq this.acReducer) && (newPlugin eq reducerPlugin))
      this
    else
      new ReduceWithConjunction(newAC, predReducer, newPlugin, order)
  
  private def replacePred(newPred : ReduceWithPredLits)
                         : ReduceWithConjunction =
    if (newPred eq this.predReducer)
      this
    else
      new ReduceWithConjunction(acReducer, newPred, reducerPlugin, order)

  private def replacePlugin(newPlugin : ReducerPlugin)
                         : ReduceWithConjunction =
    if (newPlugin eq reducerPlugin)
      this
    else
      new ReduceWithConjunction(acReducer, predReducer, newPlugin, order)
  
  private def reduce(ac : ArithConj,
                     logger : ComputationLogger)
                    : (ArithConj, ReduceWithConjunction) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (newArithConj, newACReducer) = acReducer.reduceAndAdd(ac, logger)
    if (newArithConj.isFalse) throw FALSE_EXCEPTION
    (newArithConj,
     this.replace(newACReducer,
                  reducerPlugin.addAssumptions(
                                    newArithConj,
                                    ReducerPlugin.ReductionMode.Contextual)))
  }

  private def plainReduce(ac : ArithConj)
                         : (ArithConj, ReduceWithConjunction) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val (newAC, newRed) = acReducer plainReduce ac
    (newAC,
     replace(newRed,
             reducerPlugin.addAssumptions(
                                newAC,
                                ReducerPlugin.ReductionMode.Simple)))
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

  private def reduceWithPlugin(conj : PredConj, logger : ComputationLogger,
                               mode : ReducerPlugin.ReductionMode.Value)
                              : Either[ReduceWithConjunction,
                                       ReducerPlugin.ChangedConjResult] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithConjunction.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (conj.isTrue) {
      Left(this)
    } else reducerPlugin.reduce(conj, this, logger, mode) match {
      case ReducerPlugin.UnchangedResult =>
        Left(replacePlugin(reducerPlugin.addAssumptions(conj, mode)))
      case ReducerPlugin.FalseResult =>
        throw FALSE_EXCEPTION
      case res : ReducerPlugin.ChangedConjResult =>
        Right(res)
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
