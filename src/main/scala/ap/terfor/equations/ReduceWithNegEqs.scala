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

package ap.terfor.equations;

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.VariableShiftSubst
import ap.terfor.inequalities.InEqConj
import ap.util.{Debug, LazyMappedSet, UnionSet, Seqs, FilterIt}

object ReduceWithNegEqs {

  private val AC = Debug.AC_PROPAGATION

  def apply(eqs : scala.collection.Set[LinearCombination],
            order : TermOrder) : ReduceWithNegEqs =
    new ReduceWithNegEqs(eqs,
                         eqs exists { lc => !lc.variables.isEmpty },
                         order)
  
  def apply(eqs : NegEquationConj, order : TermOrder) : ReduceWithNegEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    new ReduceWithNegEqs(eqs.toSet, !eqs.variables.isEmpty, order)
  }
}

class ReduceWithNegEqs private (equations : scala.collection.Set[LinearCombination],
                                containsVariables : Boolean,
                                order : TermOrder) {

  def addEquations(furtherEqs : scala.collection.Set[LinearCombination])
                                               : ReduceWithNegEqs =
    if (furtherEqs.isEmpty)
      this
    else
      new ReduceWithNegEqs(UnionSet(equations, furtherEqs),
                           containsVariables || (
                             furtherEqs exists { lc => !lc.variables.isEmpty }),
                           order)

  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithNegEqs =
    if (containsVariables && num > 0)
      new ReduceWithNegEqs(
            new LazyMappedSet(
                 equations,
                 VariableShiftSubst.upShifter[LinearCombination](num, order),
                 VariableShiftSubst.downShifter[LinearCombination](num, order)),
            true,
            order)
    else
      this
 
                     
  def apply(conj : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
     
    val res =
      if (Seqs.disjoint(equations, conj.toSet))
        conj
      else
        EquationConj.FALSE

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithNegEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : NegEquationConj) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (equations.isEmpty)
        conj
      else
        conj.updateEqsSubset(conj filter ((lc:LinearCombination) =>
                                               !(equations contains lc)))(order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithNegEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : InEqConj) : InEqConj =
    apply(conj, ComputationLogger.NonLogger)

  def apply(conj : InEqConj, logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
     
    val res =
      if (equations.isEmpty) {
        conj
      } else {
        var changed = false
        
        val reducedLCs =
          for (lc <- conj) yield strengthenInEq(lc, logger) match {
            case null =>
              lc
            case strengthenedLC => {
              changed = true
              strengthenedLC
            }
          }

        /*
          Adding the following inequalities sometimes improves performance,
          but also destroys the property (res eq conj) || (res != conj)
          in ReduceWithConjunction.tentativeReduce

        val addedLCs =
          for (lc <- conj.geqZeroInfs;
               strengthenedLC = strengthenInEq(lc, logger);
               if strengthenedLC != null)
          yield {
            changed = true
            strengthenedLC
          }
        */

        if (changed)
          InEqConj(reducedLCs.iterator /* ++ addedLCs.iterator */,
                   logger, order)
        else
          conj
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithNegEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  private def strengthenInEq(lc : LinearCombination,
                             logger : ComputationLogger) : LinearCombination = {
    var strengthenedLC = lc
    
    while (equations contains strengthenedLC.makePositive) {
      val oriLC = strengthenedLC
      strengthenedLC = strengthenedLC + IdealInt.MINUS_ONE
      logger.directStrengthen(oriLC, oriLC.makePositive, strengthenedLC, order)
    }

    if (lc eq strengthenedLC)
      null
    else
      strengthenedLC
  }

}
