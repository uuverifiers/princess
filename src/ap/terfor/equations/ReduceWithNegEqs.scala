/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
    new ReduceWithNegEqs(eqs, order)
  
  
  def apply(eqs : NegEquationConj, order : TermOrder) : ReduceWithNegEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    ReduceWithNegEqs(eqs.toSet, order)
  }
}

class ReduceWithNegEqs private (equations : scala.collection.Set[LinearCombination],
                                order : TermOrder) {

  def addEquations(furtherEqs : scala.collection.Set[LinearCombination])
                                               : ReduceWithNegEqs =
    if (furtherEqs.isEmpty)
      this
    else
      ReduceWithNegEqs(UnionSet(equations, furtherEqs), order)

  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithNegEqs =
    ReduceWithNegEqs(new LazyMappedSet(
                       equations,
                       VariableShiftSubst.upShifter[LinearCombination](num, order),
                       VariableShiftSubst.downShifter[LinearCombination](num, order)),
                     order)
 
                     
  def apply(conj : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
     
    if (Seqs.disjoint(equations, conj.toSet))
      conj
    else
      EquationConj.FALSE
  }

  def apply(conj : NegEquationConj) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (equations.isEmpty)
      conj
    else
      conj.updateEqsSubset(conj filter ((lc:LinearCombination) =>
                                             !(equations contains lc)))(order)
  }

  def apply(conj : InEqConj) : InEqConj =
    apply(conj, ComputationLogger.NonLogger)

  def apply(conj : InEqConj, logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithNegEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
     
    if (equations.isEmpty)
      conj
    else
      conj.updateGeqZero(for (lc <- conj) yield {
                           var strengthenedLC = lc
                           while (equations contains strengthenedLC.makePositive) {
                             val oriLC = strengthenedLC
                             strengthenedLC = strengthenedLC + IdealInt.MINUS_ONE
                             logger.directStrengthen(oriLC, oriLC.makePositive,
                                                     strengthenedLC, order)
                           }
                           strengthenedLC
                         },  logger)(order)
  }

}
