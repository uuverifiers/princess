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

import scala.collection.mutable.ArrayBuffer

import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.util.{Debug, Logic, FilterIt, Seqs}

object NegEquationConj {
  
  val AC = Debug.AC_EQUATIONS

  /**
   * Create an equation conjunction from an arbitrary set of equations
   * (left-hand sides).
   */
  def apply(lhss : Iterable[LinearCombination], order : TermOrder) : NegEquationConj =
    lhss match {
      case lhss : Collection[LinearCombination] if (lhss.isEmpty) =>
        TRUE
      case lhss : Collection[LinearCombination] if (lhss.size == 1) =>
        apply(lhss.elements.next, order)
      case _ => 
        apply(lhss.elements, order)
    }

  def apply(lhs : LinearCombination, order : TermOrder) : NegEquationConj =
    if (lhs.isZero)
      FALSE
    else if (lhs.isNonZero)
      TRUE
    else
      new NegEquationConj(Array(lhs.makePrimitiveAndPositive), order)

  /**
   * Create an equation conjunction from an arbitrary set of equations
   * (left-hand sides).
   */
  def apply(lhss : Iterator[LinearCombination], order : TermOrder) : NegEquationConj =
    Seqs.filterAndSort[LinearCombination](lhss,
                                          l => l.isNonZero, l => l.isZero,
                                          l => l.makePrimitiveAndPositive,
                                          (a, b) => order.compare(a, b) > 0) match {
    case Seqs.FilteredSorted(sortedLhss) => {
      val contractedLhss = Seqs.removeDuplicates(sortedLhss).toArray
      new NegEquationConj (contractedLhss, order)
    }
    case Seqs.FoundBadElement(_) => FALSE
    }

  val TRUE : NegEquationConj = new NegEquationConj (Array(), TermOrder.EMPTY)

  val FALSE : NegEquationConj = new NegEquationConj (Array(LinearCombination.ZERO),
                                                     TermOrder.EMPTY)


  /**
   * Compute the conjjunction of a number of conjunctions.
   * TODO: This could be optimised much more.
   */
  def conj(conjs : Iterator[NegEquationConj], order : TermOrder) : NegEquationConj =
    Formula.conj(conjs, TRUE, (nonTrivialConjs:RandomAccessSeq[NegEquationConj]) => {
                   //-BEGIN-ASSERTION-//////////////////////////////////////////
                   Debug.assertPre(AC, Logic.forall(for (c <- nonTrivialConjs.elements)
                                                    yield (c isSortedBy order)))
                   //-END-ASSERTION-////////////////////////////////////////////
                   apply(for (c <- nonTrivialConjs.elements; lhs <- c.elements)
                         yield lhs,
                         order)
                 } )
   
  def conj(conjs : Iterable[NegEquationConj], order : TermOrder) : NegEquationConj =
    conj(conjs.elements, order)

}

/**
 * The class for representing disjunctions of equations (seen
 * as conjunctions of negated equations)
 */
class NegEquationConj private (_lhss : Array[LinearCombination],
                               _order : TermOrder)
      extends EquationSet(_lhss, _order) with SortedWithOrder[NegEquationConj] {

  def sortBy(newOrder : TermOrder) : NegEquationConj = {
    if (isSortedBy(newOrder))
      this
    else
      NegEquationConj(for (lc <- this.elements) yield lc.sortBy(newOrder),
                      newOrder)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update the equations of this conjunction; if nothing has changed,
   * <code>this</code> is returned
   */
  def updateEqs(newEqs : Seq[LinearCombination])(implicit newOrder : TermOrder)
               : NegEquationConj =
    if (Seqs.subSeq(newEqs.elements, this.elements)) {
      if (newEqs.size == this.size)
        this
      else
        new NegEquationConj (newEqs.toArray, newOrder)
    } else {
      NegEquationConj(newEqs, newOrder)
    }
      
  /**
   * Update the equations of this conjunction under the assumption that the
   * new equations form a subset of the old equations
   */
  def updateEqsSubset(newEqs : Seq[LinearCombination])(implicit newOrder : TermOrder)
                     : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(NegEquationConj.AC, Seqs.subSeq(newEqs.elements, this.elements))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (newEqs.size == this.size)
      this
    else
      new NegEquationConj (newEqs.toArray, newOrder)
  }
         
  //////////////////////////////////////////////////////////////////////////////

  def isTrue : Boolean = this.isEmpty

  /**
   * The only allowed case of obviously unsatisfiable conjunctions of negated
   * equations is the one of a single equation 0!=0
   */
  def isFalse : Boolean = (!isEmpty && this(0).isZero)

  /**
   * Create the negation of at most one negated equation
   */
  def negate : EquationConj = {
    if (this.isTrue) {
      EquationConj.FALSE
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(NegEquationConj.AC, this.size == 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      EquationConj(this(0), order)
    }
  }

  protected val relationString : String = "!="

  //////////////////////////////////////////////////////////////////////////////
     
  override def equals(that : Any) : Boolean = that match {
    case that : NegEquationConj => super.equals(that)
    case _ => false
  }

  override def hashCode = (super.hashCode + 364783671)
}
