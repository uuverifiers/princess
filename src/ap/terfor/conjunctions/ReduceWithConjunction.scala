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

package ap.terfor.conjunctions;

import ap.basetypes.IdealInt
import ap.terfor._
import ap.terfor.arithconj.{ArithConj, ReduceWithAC, ModelElement}
import ap.terfor.equations.EquationConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
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
                    (currentPredConj eq res.predConj) &&
                    (currentNegConjs eq res.negatedConjs)) {
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
                  // the reduction has made some new equations available, continue
                  // in the outer loop

                  currentArithConj =
                    ArithConj.conj(Iterator(currentArithConj, addArithConj),
                                   logger, order)
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
            currentArithConj =
              ArithConj.conj(Iterator(currentArithConj, newEqs),
                             logger, order)
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

      case Some(Quantifier.EX)
        if (newArithConj.isLiteral &&
              newPredConj.isTrue &&
              newNegConjs.isTrue &&
              newArithConj.positiveEqs.size == 1 &&
              newArithConj.positiveEqs.head.leadingTerm == VariableTerm(0)) => {

          val res = normDivisibilityConstraint(quans, newArithConj, order)
          if (oldConj != null && res == oldConj)
            oldConj
          else
            res
        }

      case Some(Quantifier.EX) => {
        // Try to eliminate literals

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
      
      // Check whether the negated version of a quantified literal can be
      // simplified further
      case Some(Quantifier.ALL)
          if (newArithConj.isLiteral &&
                newPredConj.isTrue &&
                newNegConjs.isTrue) => {

          // TODO: in which cases can this really work?

          val res =
            constructConj(null,
                          for (q <- quans) yield q.dual,
                          newArithConj.negate,
                          PredConj.TRUE, NegatedConjunctions.TRUE,
                          order).negate
          if (oldConj != null && res == oldConj)
            oldConj
          else
            res
      }
      
      // Check whether the negated version of a quantified literal can be
      // simplified further
      case Some(Quantifier.ALL)
          if (newArithConj.isTrue &&
                newPredConj.isTrue &&
                newNegConjs.size == 1) => {

          // TODO: in which cases can this really work?

          val subConj = newNegConjs(0)

          val res =
            constructConj(null,
                          subConj.quans ++ (for (q <- quans) yield q.dual),
                          subConj.arithConj,
                          subConj.predConj, subConj.negatedConjs,
                          order).negate

          if (oldConj != null && res == oldConj)
            oldConj
          else
            res
      }
      
      case _ =>
        createConj(oldConj, quans,
                   newArithConj, newPredConj, newNegConjs, order)
    }

  private def normDivisibilityConstraint(quans : Seq[Quantifier],
                                         arithConj : ArithConj,
                                         order : TermOrder)
                                       : Conjunction = {
    val eq = arithConj.positiveEqs.head

    if (eq.leadingCoeff.isUnit) {
      // This literal can directly be eliminated
      Conjunction.TRUE
    } else {
      // Try to simplify the divisibility constraint

      val newEq  = normDivisibilityLC(eq, order)
      val newEqs = EquationConj(newEq, order)

      if (newEqs.head.leadingCoeff.isUnit) {
        Conjunction.TRUE
      } else {
        val newAC = arithConj.updatePositiveEqs(newEqs)(order)
        Conjunction(quans, newAC, PredConj.TRUE,
                    NegatedConjunctions.TRUE,
                    order)
      }
    }
  }

  private def normDivisibilityLC(eq1 : LinearCombination, order : TermOrder)
                               : LinearCombination = {
    val eq2 = eq1.moduloLeadingCoeff

    // ensure that the leading coefficient and the coefficient of the
    // second term have different signs
    val eq3 =
      if (eq2.size >= 2 &&
            eq2.leadingCoeff > IdealInt(2) &&
            (eq2 getCoeff 1).signum < 0) {
        val it = eq2.pairIterator
        val (c, t) = it.next
        LinearCombination.createFromSortedSeq(Iterator((-c, t)) ++ it, order)
      } else {
        eq2
      }

    eq3
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
    Debug.warnIfNotPostFast(
      ReduceWithConjunction.AC,
      (ReduceWithConjunction.reduceConj(res, this, logger) eq res) &&
        ((res eq conj) || (res != conj)),
      "reduction of formula did not converge: " + conj)
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
    Debug.warnIfNotPostFast(
      ReduceWithConjunction.AC,
      ((res eq conj) || (res != conj)) &&
        // if the input had been reduced at some previous point,
        // it is guaranteed to be fully reduced now
        (!(withoutFacts(conj) eq conj) || (apply(res) eq res)),
      "reduction of formula did not converge: " + conj)
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
    Debug.warnIfNotPostFast(
      ReduceWithConjunction.AC,
      Logic.forall(for (c <- res.iterator) yield (this(c) eq c)) &&
        ((res eq conjs) || (res != conjs)),
      "reduction of formula did not converge: " + conjs)
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
   * Check whether the known inequalities imply a lower bound of the given term.
   * Also return assumed inequalities needed to derive the bound.
   */
  def lowerBoundWithAssumptions(t : Term)
      : Option[(IdealInt, Seq[LinearCombination])] =
    acReducer lowerBoundWithAssumptions t

  /**
   * Check whether the known inequalities imply a lower bound of the given term.
   * If <code>withAssumptionInEqs</code> is set, also return the assumed
   * inequalities needed for the bound.
   */
  def lowerBound(t : Term, withAssumptionInEqs : Boolean)
      : Option[(IdealInt, Seq[InEqConj])] =
    if (withAssumptionInEqs)
      for ((b, lcs) <- lowerBoundWithAssumptions(t))
      yield (b, for (lc <- lcs) yield InEqConj(lc, order))
    else
      for (b <- lowerBound(t))
      yield (b, List())

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

  /**
   * Check whether the known inequalities imply an upper bound of the given
   * term. Also return assumed inequalities needed to derive the bound.
   */
  def upperBoundWithAssumptions(t : Term)
      : Option[(IdealInt, Seq[LinearCombination])] =
    acReducer upperBoundWithAssumptions t

  /**
   * Check whether the known inequalities imply a upper bound of the given term.
   * If <code>withAssumptionInEqs</code> is set, also return the assumed
   * inequalities needed for the bound.
   */
  def upperBound(t : Term, withAssumptionInEqs : Boolean)
      : Option[(IdealInt, Seq[InEqConj])] =
    if (withAssumptionInEqs)
      for ((b, lcs) <- upperBoundWithAssumptions(t))
      yield (b, for (lc <- lcs) yield InEqConj(lc, order))
    else
      for (b <- upperBound(t))
      yield (b, List())

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
      val (redConj, newEqs) = predReducer(acReducer(conj, logger), logger)
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
    val logger = ComputationLogger.NonLogger
    val (redConj, newEqs) =
      predReducer(acReducer(conj, logger), logger)
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
