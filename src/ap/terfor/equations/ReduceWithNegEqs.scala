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
        val reducedLCs = for (lc <- conj) yield {
                           var strengthenedLC = lc
                           while (equations contains strengthenedLC.makePositive) {
                             val oriLC = strengthenedLC
                             strengthenedLC = strengthenedLC + IdealInt.MINUS_ONE
                             logger.directStrengthen(oriLC, oriLC.makePositive,
                                                     strengthenedLC, order)
                             changed = true
                           }
                           strengthenedLC
                         }

        if (changed)
          InEqConj(reducedLCs.iterator, logger, order)
        else
          conj
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithNegEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

}
