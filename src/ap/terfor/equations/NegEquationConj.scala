/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.ArrayBuffer

import ap.terfor._
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
    if (lhss.isEmpty)
      TRUE
    else if (lhss.size == 1)
      apply(lhss.head, order)
    else
      apply(lhss.iterator, order)

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
    Formula.conj(conjs, TRUE, (nonTrivialConjs:IndexedSeq[NegEquationConj]) => {
                   //-BEGIN-ASSERTION-//////////////////////////////////////////
                   Debug.assertPre(AC, Logic.forall(for (c <- nonTrivialConjs.iterator)
                                                    yield (c isSortedBy order)))
                   //-END-ASSERTION-////////////////////////////////////////////
                   apply(for (c <- nonTrivialConjs.iterator; lhs <- c.iterator)
                         yield lhs,
                         order)
                 } )
   
  def conj(conjs : Iterable[NegEquationConj], order : TermOrder) : NegEquationConj =
    conj(conjs.iterator, order)

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
      NegEquationConj(for (lc <- this.iterator) yield lc.sortBy(newOrder),
                      newOrder)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update the equations of this conjunction; if nothing has changed,
   * <code>this</code> is returned
   */
  def updateEqs(newEqs : Seq[LinearCombination])(implicit newOrder : TermOrder)
               : NegEquationConj =
    if (Seqs.subSeq(newEqs.iterator, this.iterator)) {
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
    Debug.assertPre(NegEquationConj.AC, Seqs.subSeq(newEqs.iterator, this.iterator))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (newEqs.size == this.size)
      this
    else
      new NegEquationConj (newEqs.toArray, newOrder)
  }
         
  //////////////////////////////////////////////////////////////////////////////

  def --(that : NegEquationConj) : NegEquationConj =
    if (that.isTrue)
      this
    else
      updateEqsSubset(Seqs.diff(this, that)(order.lcOrdering)._2)(order)

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
