/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.arithconj;

import ap.basetypes.IdealInt
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
    val (newNegEqs, additionalInEqs) = reducer.reduce(ac.negativeEqs, logger)

    if ((newPosEqs eq ac.positiveEqs) &&
        (newNegEqs eq ac.negativeEqs) &&
        (newInEqs eq ac.inEqs)) {
      // then nothing has changed, and we can give back the old object
      (ac, reducer addEquations newNegEqs)
    } else if (!additionalInEqs.isEmpty) {
      // some disequalities were turned into inequalities, recurse
      val allInEqs =
        InEqConj.conj(Seqs.doubleIterator(newInEqs, additionalInEqs),
                      logger, reducer.order)
      val newAC =
        ArithConj(newPosEqs, newNegEqs, allInEqs, reducer.order)
      reduceAC(newAC, initialReducer, logger)
    } else {
      val newAC = ArithConj(newPosEqs, newNegEqs, newInEqs, reducer.order)
      if ((newInEqs.equalityInfs.isEmpty ||
             // due to bounded generated of inequality inferences,
             // it can happen that still equations are implied,
             // and further iterations will change nothing.
             // to prevent infinite looping at this point,
             // see whether anything changed
             newInEqs.equalityInfs == ac.inEqs.equalityInfs) &&
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
    if (eqs2.isTrue) {
      reduce(eqs1)
    } else if (eqs1.isTrue) {
      reduce(eqs2)
    } else {
      val res = reduce(EquationConj.conj(Array(eqs1, eqs2), logger, order))
      if (res == eqs1) eqs1 else res
    }

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
                     logger : ComputationLogger)
                    : (NegEquationConj, InEqConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (eqs.isTrue) {
      (eqs, InEqConj.TRUE)
    } else {
      val res = inEqs(negativeEqs(positiveEqs(eqs, logger)), logger)
      if (res._1.isFalse) throw FALSE_EXCEPTION_STD
      res
    }
  }

  private def reduce(ies : InEqConj,
                     logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithAC.AC, ies isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (ies.isTrue) {
        ies
      } else {
        val preInEqs = negativeEqs(positiveEqs(ies, logger), logger)
        if (preInEqs.equalityInfs.isEmpty) {
          val redInEqs = inEqs reduceNoEqualityInfs preInEqs
          if (redInEqs.isFalse) throw FALSE_EXCEPTION_STD
          // it can happen that the last reduction step leads to a conjunction
          // that coincides with the original one
          if (!(redInEqs eq preInEqs) && redInEqs == ies)
            ies
          else
            redInEqs
        } else {
          // if the inequalities imply equations, we first have
          // to include those in the equations of the overall
          // ArithConj
          if (preInEqs.isFalse) throw FALSE_EXCEPTION_STD
          preInEqs
        }
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithAC.AC, (res eq ies) || (res != ies))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
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
  def plainReduce(conj : ArithConj) : (ArithConj, ReduceWithAC) = try {
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

    val newReducer =
      this addInEqs newInEqs
    val (newNegEqs, additionalInEqs) =
      newReducer.reduce(conj.negativeEqs, ComputationLogger.NonLogger)

    if ((newEqs    eq conj.positiveEqs) &&
        (newNegEqs eq conj.negativeEqs) &&
        (newInEqs  eq conj.inEqs)) {
      (conj, newReducer)
    } else {
      val allInEqs =
        InEqConj.conj(Seqs.doubleIterator(newInEqs, additionalInEqs), order)
      (ArithConj(newEqs, newNegEqs, allInEqs, order), newReducer)
    }
  }
  catch { case _ : FALSE_EXCEPTION => (ArithConj.FALSE, this) }

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

  /**
   * Check whether known inequalities imply a lower bound of the given term.
   */
  def lowerBound(t : Term) : Option[IdealInt] = inEqs lowerBound t

  /**
   * Check whether the known inequalities imply a lower bound of the given term.
   * Also return assumed inequalities needed to derive the bound.
   */
  def lowerBoundWithAssumptions(t : Term)
      : Option[(IdealInt, Seq[LinearCombination])] =
    inEqs lowerBoundWithAssumptions t

  /**
   * Check whether known inequalities imply an upper bound of the given
   * term.
   */
  def upperBound(t : Term) : Option[IdealInt] = inEqs upperBound t

  /**
   * Check whether the known inequalities imply an upper bound of the given
   * term. Also return assumed inequalities needed to derive the bound.
   */
  def upperBoundWithAssumptions(t : Term)
      : Option[(IdealInt, Seq[LinearCombination])] =
    inEqs upperBoundWithAssumptions t

}

private abstract class FALSE_EXCEPTION extends Exception

private object FALSE_EXCEPTION_STD extends FALSE_EXCEPTION 

private case class FALSE_EXCEPTION_PRED(conj : PredConj) extends FALSE_EXCEPTION
