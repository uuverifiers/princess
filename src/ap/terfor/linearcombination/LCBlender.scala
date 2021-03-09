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

package ap.terfor.linearcombination;

import scala.collection.mutable.{PriorityQueue, Buffer, ArrayBuffer}

import ap.terfor._
import ap.basetypes.IdealInt
import ap.util.{PeekIterator, PriorityQueueWithIterators, Debug}

/**
 * Class for mixing together a number of <code>LinearCombination</code>s that
 * are sorted by the same <code>TermOrder</code> (namely by <code>order</code>)
 */
class LCBlender(order : TermOrder) extends PeekIterator[(IdealInt,Term)] {
  
  private val AC = Debug.AC_LINEAR_COMB
   
  private implicit val orderPairs = new Ordering[(IdealInt,Term)] {
    def compare(thisTerm : (IdealInt,Term), thatTerm : (IdealInt,Term)) =
      order.compare(thisTerm _2, thatTerm _2)
  }
   
  private val terms = new PriorityQueueWithIterators[(IdealInt,Term)]
  
  def +=(coeff : IdealInt, lc : LinearCombination) : Unit = {
    if (nextVal != null) terms += nextVal

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, lc isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    terms += ScalingIterator(coeff, lc.pairIterator)
    nextVal = computeNext
  }
  
  def +=(coeff1 : IdealInt, lc1 : LinearCombination,
         coeff2 : IdealInt, lc2 : LinearCombination) : Unit = {
    if (nextVal != null) terms += nextVal

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (lc1 isSortedBy order) && (lc2 isSortedBy order))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    terms += ScalingIterator(coeff1, lc1.pairIterator)
    terms += ScalingIterator(coeff2, lc2.pairIterator)
    nextVal = computeNext
  }
  
  def ++=(lcs : Iterable[(IdealInt, LinearCombination)]) : Unit = {
    if (nextVal != null) terms += nextVal

    for ((coeff, lc) <- lcs) {

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, lc isSortedBy order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      terms += ScalingIterator(coeff, lc.pairIterator)
    }

    nextVal = computeNext
  }
  
  /**
   * Extract the next monomial from the priority queue, return <code>null</code>
   * if the queue does not contain any further non-zero monomials. If the result
   * is not <code>null</code>, it is guaranteed that the queue only contains
   * monomials that are strictly smaller than the returned monomial
   */
  private def computeNext : (IdealInt,Term) = {
    while (!terms.isEmpty) {
      val (firstC, firstT) = terms.next

      var currentCoeff = firstC
      while (!terms.isEmpty && (terms.max _2) == firstT) {
        val nextC = (terms.next _1)
        currentCoeff = currentCoeff + nextC
      }
     
      if (!currentCoeff.isZero) return (currentCoeff, firstT)
    }
    
    null
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val resultBuf : Buffer[(IdealInt,Term)] = new ArrayBuffer

  def result : LinearCombination =
    LinearCombination.createFromSortedSeq(resultBuf, order)
  
  private var nextVal : (IdealInt,Term) = computeNext
  
  def hasNext = (nextVal != null)
  
  def next = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC,
                    resultBuf.isEmpty ||
                    order.compare(resultBuf.last _2, nextVal _2) > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    resultBuf += nextVal
    val res = nextVal
    nextVal = computeNext
    res
  }
  
  def peekNext = nextVal

}
