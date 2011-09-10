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
import ap.basetypes.IdealInt
import ap.terfor.substitutions.{Substitution, ConstantSubst, ComposeSubsts}
import ap.terfor.linearcombination.LinearCombination
import ap.util.Debug

object ModelFinder {
  
  private val AC = Debug.AC_MODEL_FINDER
  
}

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>ArithConj</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
class ModelFinder(ac : ArithConj, c : ConstantTerm)
      extends ((Substitution, TermOrder) => Substitution) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // The handled cases: either a single positive equation, or a conjunction
  // of negated equations and inequalities
  Debug.assertCtor(ModelFinder.AC,
                   ac.positiveEqs.size == 1 && ac.size == 1 ||
                   ac.positiveEqs.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
   
  def apply(subst : Substitution, order : TermOrder) : Substitution = {
    val res = if (ac.positiveEqs.isEmpty)
                solveInNegEqs(subst, order)
              else
                solveEquation(subst, order)
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ModelFinder.AC, res(ac).isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  private def solveInNegEqs(subst : Substitution, order : TermOrder) : Substitution = {
    val (instantiatedAC, extendedSubst) = insertKnownValues(subst, ac, order)

    val negEqs = instantiatedAC.negativeEqs
    val inEqs = instantiatedAC.inEqs
      
    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertInt(ModelFinder.AC,
                    inEqs.size <= 2 && (instantiatedAC.constants subsetOf Set(c)) &&
                    (inEqs.isEmpty || (inEqs(0) get c).abs.isOne))
    //-END-ASSERTION-/////////////////////////////////////////////////////////
    
    // seach for the right value (we know that one must exist ...)
    var value =
      if (inEqs.isEmpty) IdealInt.ZERO else (-inEqs(0).constant * (inEqs(0) get c))
    val step = if (inEqs.isEmpty) IdealInt.ONE else (inEqs(0) get c)
    
    val valueSubst = {
      var res : Substitution = null
      do {
        res = ConstantSubst(c, LinearCombination(value), order)
        value = value + step
      } while (res(negEqs).isFalse)
      res
    }

    ComposeSubsts(Array(extendedSubst, valueSubst), order)
  }
  
  private def solveEquation(subst : Substitution, order : TermOrder) : Substitution = {
    val (instantiatedEq, extendedSubst) =
      insertKnownValues(subst, ac.positiveEqs, order)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////
    Debug.assertPost(ModelFinder.AC,
                     instantiatedEq.size == 1 &&
                     instantiatedEq.constants == Set(c) &&
                     (instantiatedEq(0) get c).isOne)
    //-END-ASSERTION-///////////////////////////////////////////////////
    val value = -instantiatedEq(0).constant
    val valueSubst = ConstantSubst(c, LinearCombination(value), order)
    ComposeSubsts(Array(extendedSubst, valueSubst), order)
  }

  private def insertKnownValues[A <: TerFor]
                               (values : Substitution,
                                eliminatedFor : A,
                                order : TermOrder) : (A, Substitution) = {
    val instantiatedFor = values(eliminatedFor)
    //it might be that the formulas contains further constants apart
    //from c, we eliminate them by replacing them with 0
    val furtherConstsZero =
      ConstantSubst(Map() ++ (for (d <- (instantiatedFor.constants - c).iterator)
                              yield (d -> LinearCombination.ZERO)), order)

    (furtherConstsZero(instantiatedFor).asInstanceOf[A],
     ComposeSubsts(values, furtherConstsZero, order))
  }

}
