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

package ap.terfor.arithconj;

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions}
import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithEqs,
                            ReduceWithNegEqs}
import ap.terfor.inequalities.{InEqConj, ReduceWithInEqs}
import ap.terfor.preds.{Atom, PredConj}
import ap.util.{Debug, Seqs, FilterIt}

object ReduceWithAC {
  
  private val AC = Debug.AC_PROPAGATION

  def apply(ac : ArithConj, order : TermOrder) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    new ReduceWithAC(ReduceWithEqs(ac.positiveEqs, order),
                     ReduceWithNegEqs(ac.negativeEqs, order),
                     ReduceWithInEqs(ac.inEqs, order),
                     order)
  }

  def apply(inEqs : ReduceWithInEqs, order : TermOrder) : ReduceWithAC =
    new ReduceWithAC(ReduceWithEqs(EquationConj.TRUE, order), 
                     ReduceWithNegEqs(NegEquationConj.TRUE, order),
                     inEqs,
                     order)

  //////////////////////////////////////////////////////////////////////////////
  // Some of the "static" methods of the <code>ReduceWithAC</code>-class
  // These are methods juggling with different reducer-objects

  /**
   * Reduce a conjunction of arithmetic stuff and return the reduced conjunction,
   * together with a new <code>ReduceWithAC</code> object to which the reduced
   * conjunction was added.
   */
  private def reduceAC(ac : ArithConj,
                       initialReducer : ReduceWithAC,
                       logger : ComputationLogger) : (ArithConj, ReduceWithAC) = {

    // positive equations always come first
    val newPosEqs =
      initialReducer.reduce(ac.positiveEqs, ac.inEqs.equalityInfs, logger)
    var reducer = initialReducer addEquations newPosEqs

    // then, reduce inequalities, assuming the (unreduced) negated equations
    val newInEqs = (reducer addEquations ac.negativeEqs).reduce(ac.inEqs, logger)
    reducer = reducer addInEqs newInEqs

    // reduce negated equations, assuming the reduced inequalities
    val newNegEqs = reducer.reduce(ac.negativeEqs, logger)

    if ((newPosEqs eq ac.positiveEqs) &&
        (newNegEqs eq ac.negativeEqs) &&
        (newInEqs eq ac.inEqs)) {
      // then nothing has changed, and we can give back the old object
      (ac, reducer addEquations newNegEqs)
    } else {
      val newAC = ArithConj(newPosEqs, newNegEqs, newInEqs, reducer.order)
      if ((newInEqs.equalityInfs.isEmpty /* ||
             newInEqs.equalityInfs == ac.inEqs.equalityInfs */) &&
          (newNegEqs eq ac.negativeEqs))
        (newAC, reducer addEquations newNegEqs)
      else
        // if the new inequalities still imply equations, we have to reduce once
        // more. note that we again start with the reducer <code>initialReducer</code> 
        reduceAC(newAC, initialReducer, logger)
    }
  }

}

class ReduceWithAC private (positiveEqs : ReduceWithEqs,
                            negativeEqs : ReduceWithNegEqs,
                            inEqs : ReduceWithInEqs,
                            private val order : TermOrder) {

  def passQuantifiers(num : Int) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, num >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (num == 0) {
      this
    } else {
      val new1 = positiveEqs passQuantifiers num
      val new2 = negativeEqs passQuantifiers num
      val new3 = inEqs passQuantifiers num

      if ((new1 eq positiveEqs) && (new2 eq negativeEqs) && (new3 eq inEqs))
        this
      else
        new ReduceWithAC(new1, new2, new3, order)
    }
  }

  def addArithConj(ac : ArithConj) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, ac isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (ac.isEmpty)
      this
    else
      new ReduceWithAC(positiveEqs addEquations ac.positiveEqs.toMap,
                       negativeEqs addEquations ac.negativeEqs.toSet,
                       inEqs addInEqs ac.inEqs,
                       order)    
  }
  
  private def addEquations(eqs : EquationConj) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (eqs.isEmpty)
      this
    else
      new ReduceWithAC(positiveEqs addEquations eqs.toMap,
                       negativeEqs,
                       inEqs,
                       order)
  }
  
  private def addEquations(eqs : NegEquationConj) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (eqs.isEmpty)
      this
    else
      new ReduceWithAC(positiveEqs,
                       negativeEqs addEquations eqs.toSet,
                       inEqs,
                       order)
  }
  
  private def addInEqs(furtherInEqs : InEqConj) : ReduceWithAC = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, furtherInEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (furtherInEqs.isEmpty)
      this
    else
      new ReduceWithAC(positiveEqs,
                       negativeEqs,
                       inEqs addInEqs furtherInEqs,
                       order)    
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Methods for reducing different kinds of formulas. If any of the
  // methods detects that a resulting formula is false,
  // <code>FALSE_EXCEPTION</code> is thrown (this is done to simplify the
  // handling of <code>Conjunction</code>s)
  // TODO: optimise for cases where no reduction is possible (detect this early,
  // create no new objects)
  // TODO: define the following methods in a nicer way, polymorphic?
  
  private def reduce(eqs1 : EquationConj, eqs2 : EquationConj,
                     logger : ComputationLogger) : EquationConj =
    if (eqs2.isTrue)
      reduce(eqs1)
    else if (eqs1.isTrue)
      reduce(eqs2)
    else
      reduce(EquationConj.conj(Array(eqs1, eqs2), logger, order))

  private def reduce(eqs : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (eqs.isTrue) {
      eqs
    } else {
      val redEqs = inEqs(negativeEqs(positiveEqs(eqs)))
      if (redEqs.isFalse) throw FALSE_EXCEPTION_STD
      redEqs
    }
  }

  private def reduce(eqs : NegEquationConj,
                     logger : ComputationLogger) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (eqs.isTrue) {
      eqs
    } else {
      val redEqs = inEqs(negativeEqs(positiveEqs(eqs, logger)))
      if (redEqs.isFalse) throw FALSE_EXCEPTION_STD
      redEqs
    }
  }

  private def reduce(ies : InEqConj,
                     logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, ies isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (ies.isTrue) {
      ies
    } else {
      val preInEqs = negativeEqs(positiveEqs(ies, logger), logger)
      if (preInEqs.equalityInfs.isEmpty) {
        val redInEqs = inEqs reduceNoEqualityInfs preInEqs
        if (redInEqs.isFalse) throw FALSE_EXCEPTION_STD
        redInEqs
      } else {
        // if the inequalities imply equations, we first have
        // to include those in the equations of the overall
        // ArithConj
        if (preInEqs.isFalse) throw FALSE_EXCEPTION_STD
        preInEqs
      }
    }
  }

  private def reduce(conj : PredConj, logger : ComputationLogger) : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val redConj = positiveEqs(conj, logger)
    if (redConj.isFalse) throw FALSE_EXCEPTION_PRED(redConj)
    redConj
  }

  //////////////////////////////////////////////////////////////////////////////
    
  /**
   * Reduce an arithmetic conjunction using the information stored in this
   * object. The result is the simplified conjunction, as well as a new
   * reducer to which the information from the simplified arithmetic conjunction
   * has been added.
   */
  def reduceAndAdd(conj : ArithConj,
                   logger : ComputationLogger) : (ArithConj, ReduceWithAC) = {
    val res =
      if (conj.isTrue || conj.isFalse)
        (conj, this)
      else
        try { ReduceWithAC.reduceAC(conj, this, logger) }
        catch { case _ : FALSE_EXCEPTION => (ArithConj.FALSE, this) }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithAC.AC, (res._1 eq conj) || (res._1 != conj))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : ArithConj) : ArithConj =  {
    val res = (reduceAndAdd(conj, ComputationLogger.NonLogger) _1)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // we demand that the reducer is a projection (repeated application does not
    // change the result anymore)
    Debug.assertPostFast(ReduceWithAC.AC,
                         (reduceAndAdd(res, ComputationLogger.NonLogger) _1) eq res)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Just reduce the components of the conjunction individually,
   * do not do any internal propagation.
   */
  def plainReduce(conj : ArithConj) : ArithConj = try {
    val (newEqs, newInEqs) =
      if (conj.inEqs.equalityInfs.isTrue) {
        (reduce(conj.positiveEqs),
         reduce(conj.inEqs, ComputationLogger.NonLogger))
      } else {
        // we have to move implied equations to the equations component,
        // to avoid infinite loops in
        // <code>ReduceWithConjunction.plainReduce</code>
        val newEqs =
          reduce(conj.positiveEqs, conj.inEqs.equalityInfs,
                 ComputationLogger.NonLogger)
        val newInEqs = (this addEquations newEqs).reduce(
                 conj.inEqs, ComputationLogger.NonLogger)
        (newEqs, newInEqs)
      }

    val newNegEqs = reduce(conj.negativeEqs, ComputationLogger.NonLogger)

    if ((newEqs    eq conj.positiveEqs) &&
        (newNegEqs eq conj.negativeEqs) &&
        (newInEqs  eq conj.inEqs))
      conj
    else
      ArithConj(newEqs, newNegEqs, newInEqs, order)
  }
  catch { case _ : FALSE_EXCEPTION => ArithConj.FALSE }

  def apply(conj : EquationConj) : EquationConj =
    try { this reduce conj }
    catch { case _ : FALSE_EXCEPTION => EquationConj.FALSE }    

  def apply(conj : PredConj, logger : ComputationLogger) : PredConj =
    if (positiveEqs.isEmpty)
      conj
    else
      try { this.reduce(conj, logger) }
      // we use the inconsistent reduced predicate as result (because the method
      // PredConj.FALSE needs an argument)
      catch { case FALSE_EXCEPTION_PRED(falsePredConj) => falsePredConj }    
    
}

private abstract class FALSE_EXCEPTION extends Exception

private object FALSE_EXCEPTION_STD extends FALSE_EXCEPTION 

private case class FALSE_EXCEPTION_PRED(conj : PredConj) extends FALSE_EXCEPTION
