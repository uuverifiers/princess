/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.terfor.arithconj;

import ap.terfor._
import ap.terfor.equations.EquationConj
import ap.basetypes.IdealInt
import ap.terfor.substitutions.{Substitution, ConstantSubst, ComposeSubsts}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, LazyMappedMap}

import scala.collection.mutable.{HashMap => MHashMap}

object ModelElement {
  
  protected[arithconj] val AC = Debug.AC_MODEL_FINDER
  
  /**
   * Construct a model from a set of model elements, starting with the first
   * element.
   */
  def constructModel(modelElements : Seq[ModelElement],
                     order : TermOrder,
                     initialModel : Map[ConstantTerm, IdealInt] = Map())
                    : EquationConj = {
    val model = new MHashMap[ConstantTerm, IdealInt]
    model ++= initialModel
    for (m <- modelElements) m.extendModel(model, order)
    EquationConj(for ((c, value) <- model.iterator)
                   yield LinearCombination(IdealInt.ONE, c, -value, order),
                 order)
  }
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
abstract sealed class ModelElement(val cs : scala.collection.Set[ConstantTerm]) {
  /**
   * Extend the given model, in such a way that the conditions of this model
   * element are satisfied.
   */
  def extendModel(model : MHashMap[ConstantTerm, IdealInt],
                  order : TermOrder) : Unit
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
case class EqModelElement(eqs : EquationConj,
                          _cs : scala.collection.Set[ConstantTerm])
           extends ModelElement(_cs) {
  
  def extendModel(model : MHashMap[ConstantTerm, IdealInt],
                  order : TermOrder) : Unit =
    for (lc <- eqs) {
      var constant = IdealInt.ZERO
      var assignedConstant : ConstantTerm = null
      var assignedCoeff : IdealInt = null
      
      val N = lc.size
      var i = 0
      while (i < N) {
        (lc getTerm i) match {
          case c : ConstantTerm =>
            (model get c) match {
              case Some(value) =>
                constant = constant + (value * (lc getCoeff i))
              case None =>
                if (cs contains c) {
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(ModelElement.AC,
                                  assignedConstant == null &&
                                  (lc getCoeff i).isUnit)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  assignedConstant = c
                  assignedCoeff = lc getCoeff i
                } else {
                  // then we assign this constant to zero
                  model.put(c, IdealInt.ZERO)
                }
            }
          case OneTerm =>
            constant = constant + (lc getCoeff i)
        }
        
        i = i + 1
      }
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelElement.AC, assignedConstant != null)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      model.put(assignedConstant,
                if (assignedCoeff.isOne) -constant else constant)
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
case class InNegEqModelElement(ac : ArithConj, c : ConstantTerm)
           extends ModelElement(Set(c)) {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // The handled case: a conjunction of negated equations and inequalities
  Debug.assertCtor(ModelElement.AC, ac.positiveEqs.isEmpty && cs.size == 1)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def extendModel(model : MHashMap[ConstantTerm, IdealInt],
                  order : TermOrder) : Unit = {
    val replacement =
      new LazyMappedMap[ConstantTerm, IdealInt, ConstantTerm, Term](
                        model,
                        (x:ConstantTerm) => x,
                        { case x:ConstantTerm => x },
                        x => LinearCombination(x))

    val instantiatedACRaw = ConstantSubst(replacement, order)(ac)
    // it might be that the formula contains further constants apart
    // from cs, we eliminate them by replacing them with 0
    val furtherConstsZero =
      ConstantSubst((for (d <- (instantiatedACRaw.constants - c).iterator)
                     yield {
                       model.put(d, IdealInt.ZERO)
                       (d, LinearCombination.ZERO)
                     }).toMap, order)
    
    val instantiatedAC = furtherConstsZero(instantiatedACRaw)

    val negEqs = instantiatedAC.negativeEqs
    val inEqs = instantiatedAC.inEqs
      
    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertInt(ModelElement.AC,
                    inEqs.size <= 2 && (instantiatedAC.constants subsetOf Set(c)) &&
                    (inEqs.isEmpty || (inEqs(0) get c).isUnit))
    //-END-ASSERTION-/////////////////////////////////////////////////////////
    
    // seach for the right value (we know that one must exist ...)
    var value =
      if (inEqs.isEmpty) IdealInt.ZERO else (-inEqs(0).constant * (inEqs(0) get c))
    val step = if (inEqs.isEmpty) IdealInt.ONE else (inEqs(0) get c)
    
    while (ConstantSubst(c, LinearCombination(value), order)(negEqs).isFalse)
      value = value + step
    
    model.put(c, value)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ModelElement.AC, ConstantSubst(replacement, order)(ac).isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  }
}
