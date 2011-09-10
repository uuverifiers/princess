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

package ap.terfor.preds;

import ap.terfor._
import ap.terfor.substitutions.VariableShiftSubst
import ap.util.{Debug, Seqs, LazyMappedSet, UnionSet}

object ReduceWithPredLits {
  
  private val AC = Debug.AC_PROPAGATION
  
  def apply(conj : PredConj, order : TermOrder) : ReduceWithPredLits = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    new ReduceWithPredLits(conj.positiveLitsAsSet, conj.negativeLitsAsSet,
                           conj.predicates, order)
  }
    
}

class ReduceWithPredLits private (positiveLits : scala.collection.Set[Atom],
                                  negativeLits : scala.collection.Set[Atom],
                                  preds : scala.collection.Set[Predicate],
                                  order : TermOrder) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ReduceWithPredLits.AC,
                   preds == Set() ++ (for (a <- positiveLits) yield a.pred) ++
                                     (for (a <- negativeLits) yield a.pred))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def addLits(furtherLits : PredConj) : ReduceWithPredLits =
    if (furtherLits.isTrue)
      this
    else
      new ReduceWithPredLits(UnionSet(positiveLits, furtherLits.positiveLitsAsSet),
                             UnionSet(negativeLits, furtherLits.negativeLitsAsSet),
                             UnionSet(preds, furtherLits.predicates),
                             order)

  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithPredLits = {
    val upShifter = VariableShiftSubst.upShifter[Atom](num, order)
    val downShifter = VariableShiftSubst.downShifter[Atom](num, order)
    new ReduceWithPredLits(new LazyMappedSet(positiveLits, upShifter, downShifter),
                           new LazyMappedSet(negativeLits, upShifter, downShifter),
                           preds, order)
  }

  /**
   * Determine whether a formula that contains the given predicates might be
   * reducible by this reducer
   */
  def reductionPossible(conj : PredConj) : Boolean =
    !Seqs.disjoint(preds, conj.predicates)

  def apply(conj : PredConj) : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithPredLits.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (reductionPossible(conj)) {
      // TODO: should be done using binary search
      if (!Seqs.disjointSeq(positiveLits, conj.negativeLits) ||
          !Seqs.disjointSeq(negativeLits, conj.positiveLits))
        // a contradiction has been found
        PredConj.FALSE(conj)
      else
        conj.updateLitsSubset(conj.positiveLits filter ((a) => !(positiveLits contains a)),
                              conj.negativeLits filter ((a) => !(negativeLits contains a)),
                              order)
    } else {
      conj
    }
  }
  
}
