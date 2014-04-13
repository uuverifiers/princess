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

package ap.terfor.inequalities;

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.{ArithConj, ReduceWithAC}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.basetypes.IdealInt
import ap.terfor.substitutions.VariableShiftSubst
import ap.util.{Debug, Logic, Seqs, FilterIt, LRUCache}

import scala.collection.mutable.ArrayBuffer

object ReduceWithInEqs {
  
  protected[inequalities] val AC = Debug.AC_PROPAGATION

  def apply(inEqs : InEqConj, order : TermOrder) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, inEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (inEqs.isTrue)
      new ReduceWithEmptyInEqs(order)
    else
      new ReduceWithInEqsImpl(inEqs.findLowerBound _,
                              !inEqs.variables.isEmpty,
                              order)
  }
  
}

/**
 * Reduce certain terms or formulas drawing information from inequalities that
 * are assumed as facts.
 */
abstract class ReduceWithInEqs {
  
  def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs
  
  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithInEqs
  
  def apply(conj : EquationConj) : EquationConj

  /**
   * Reduce a conjunction of negated equations by removing all equations from
   * which we know that they hold anyway
   */
  def apply(conj : NegEquationConj) : NegEquationConj

  /**
   * Reduce a conjunction of inequalities. This means that subsumed inequalities
   * are removed, contradictions are detected, and possibly further equations
   * are inferred.
   */
  def apply(conj : InEqConj) : InEqConj

  /**
   * Reduce a conjunction of inequalities without implied equations.
   * (i.e., <code>conj.equalityInfs.isEmpty</code>)
   */
  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj
}

/**
 * The implementation for the trivial case that there are no inequalities
 * (this is realised as an own class for performance reasons)
 */
class ReduceWithEmptyInEqs protected[inequalities]
                           (order : TermOrder) extends ReduceWithInEqs {
  
  def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, furtherInEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (furtherInEqs.isTrue)
      this
    else
      new ReduceWithInEqsImpl(furtherInEqs.findLowerBound _,
                              !furtherInEqs.variables.isEmpty,order)
  }
  
  def passQuantifiers(num : Int) : ReduceWithInEqs = this
  
  def apply(conj : EquationConj) : EquationConj = conj

  def apply(conj : NegEquationConj) : NegEquationConj = conj

  def apply(conj : InEqConj) : InEqConj = conj

  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj = conj
}

/**
 * The standard implementation
 */
class ReduceWithInEqsImpl protected[inequalities]
                          (lowerBound : (LinearCombination) => Option[IdealInt],
                           containsVariables : Boolean,
                           order : TermOrder)
      extends ReduceWithInEqs {

  override def addInEqs(furtherInEqs : InEqConj) : ReduceWithInEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, furtherInEqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (furtherInEqs.isTrue)
      this
    else
      new ReduceWithInEqsImpl((lc:LinearCombination) => (
                              // we compute the maximum of all known lower bounds
                              (lowerBound(lc), furtherInEqs findLowerBound lc) match {
                                case (Some(c), Some(d)) => Some(c max d)
                                case (x@Some(_), _) => x
                                case (_, x@Some(_)) => x
                                case _ => None
                              }),
                              containsVariables || !furtherInEqs.variables.isEmpty,
                              order)
  }
  
  def passQuantifiers(num : Int) : ReduceWithInEqs =
    if (containsVariables && num > 0) {
      val downShifter = VariableShiftSubst.downShifter[LinearCombination](num, order)
      new ReduceWithInEqsImpl((lc:LinearCombination) => (if (downShifter isDefinedAt lc)
                                                           lowerBound(downShifter(lc))
                                                         else
                                                           None),
                              true,
                              order)
    } else {
      this
    }

  
  def apply(conj : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // the only possible inference is that the conjunction of equations is
    // unsatisfiable
    val res =
      if (conj exists (isNonZero(_)))
        EquationConj.FALSE
      else
        conj

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Determine whether we can derive from the known inequalities that the value
   * of <code>lc</code> is not zero
   */
  private def isNonZero(lc : LinearCombination) : Boolean = nonZeroCache(lc) {
    // yes, it has to be twice isPositive!
    isPositive(lowerBound(lc)) || isPositive(lowerBound(-lc))
  }

  private val nonZeroCache = new LRUCache[LinearCombination, Boolean] (5000)
    
  private def isPositive : Option[IdealInt] => Boolean = {
    case Some(d) => d.signum > 0
    case _ => false
  }
  
  
  def apply(conj : NegEquationConj) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      conj.updateEqsSubset(conj filter ((lc:LinearCombination) => !isNonZero(lc)))(order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : InEqConj) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (conj.equalityInfs.isEmpty) {
        reduceNoEqualityInfs(conj)
      } else {
        val reducer = ReduceWithAC(this, order)
        val ac = ArithConj(EquationConj.TRUE,
                           NegEquationConj.TRUE,
                           conj,
                           order)
        val acRes = reducer(ac)

        if (acRes eq ac) {
          conj
        } else {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(ReduceWithInEqs.AC,
                          acRes.negativeEqs.isEmpty &&
                          acRes.inEqs.equalityInfs.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          val res =
            InEqConj(acRes.inEqs.iterator ++
                     (for (lc <- acRes.positiveEqs.iterator;
                           a <- Seqs.doubleIterator(lc, -lc))
                      yield a), order)

          if (res == conj)
            conj
          else
            res
        }
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def reduceNoEqualityInfs(conj : InEqConj) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithInEqs.AC,
                    (conj isSortedBy order) && conj.equalityInfs.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      if (conj.isTrue || conj.isFalse) {
        conj
      } else try {
        val newLCs = new ArrayBuffer[LinearCombination]
        var changed = false

        val lcIt = conj.iterator
        while (lcIt.hasNext) {
          val lc = lcIt.next
          val negLC = -lc

          lowerBound(negLC) match {
            case Some(d) if (d.signum > 0) => 
              // contradiction
              throw CONTRADICTION_EXCEPTION
            case x => // we also need to check lower bounds
                      (lowerBound(lc), x) match {
                        case (Some(d), _) if (d.signum >= 0) => {
                          // the inequality is subsumed by a known inequality,
                          // can be removed
                          changed = true
                        }
                        case (_, Some(IdealInt.ZERO)) => {
                          // we can infer an equation from an inequality
                          // by inserting an upper bound as well
                          newLCs += lc
                          newLCs += negLC
                          changed = true
                        }
                        case _ => {
                          // we have to keep the inequality
                          newLCs += lc
                        }
                      }
          }
        }

        if (changed)
          InEqConj(newLCs, order)
        else
          conj
      } catch {
        case CONTRADICTION_EXCEPTION => InEqConj.FALSE
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithInEqs.AC, (res eq conj) || res != conj)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
}

private object CONTRADICTION_EXCEPTION extends Exception
