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

package ap.basetypes;

import ap.util.{Debug, Logic}

object MultiSet {
  
  private val AC = Debug.AC_BASE_TYPE
  
  def empty[A] = new MultiSet[A](scala.collection.immutable.HashMap.empty)
  
  private def addMultiplicity[A](multiplicities : Map[A, Int], el : (A, Int))
                                                            : Map[A, Int] = {
    val (key, mult) = el
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(MultiSet.AC, mult >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (mult == 0)
      multiplicities
    else
      multiplicities + (key -> (mult + multiplicities.getOrElse(key, 0)))    
  }

  private def removeMultiplicity[A](multiplicities : Map[A, Int], el : (A, Int))
                                                            : Map[A, Int] = {
    val (key, mult) = el
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(MultiSet.AC, mult >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (mult == 0) {
      multiplicities
    } else {
      val newMult = multiplicities.getOrElse(key, 0) - mult 
      if (newMult > 0)
        multiplicities + (key -> newMult)
      else
        multiplicities - key
    }    
  }
}

/**
 * A simple class to represent multisets
 */
class MultiSet[A] private (private val multiplicities : Map[A, Int])
      extends ((A) => Int) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(MultiSet.AC,
                   Logic.forall(for ((key, mult) <- multiplicities.iterator)
                                yield mult > 0))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def apply(key : A) : Int = multiplicities.getOrElse(key, 0)
  
  def contains(key : A) : Boolean = multiplicities contains key
  
  lazy val size : Int = (0 /: multiplicities) ((res, n) => res + (n _2))

  lazy val supp : scala.collection.Set[A] = multiplicities.keySet
  
  //////////////////////////////////////////////////////////////////////////////

  private def updateMultiplicities(newMults : Map[A, Int]) : MultiSet[A] =
    if (multiplicities eq newMults)
      this
    else
      new MultiSet(newMults)
  
  //////////////////////////////////////////////////////////////////////////////

  def +(el : (A, Int)) : MultiSet[A] =
    updateMultiplicities(MultiSet.addMultiplicity(multiplicities, el))

  def +(el : A) : MultiSet[A] = this.+(el, 1)

  def ++(els : Iterator[(A, Int)]) : MultiSet[A] =
    updateMultiplicities((multiplicities /: els) ((m, el) =>
                                MultiSet.addMultiplicity(m, el)))

  def ++(els : Iterable[(A, Int)]) : MultiSet[A] =
    ++(els.iterator)

  def +++(els : Iterator[A]) : MultiSet[A] =
    ++(for (el <- els) yield (el, 1))

  def +++(els : Iterable[A]) : MultiSet[A] =
    ++(for (el <- els.iterator) yield (el, 1))

  def ++(els : MultiSet[A]) : MultiSet[A] =
    ++(els.multiplicities.iterator)

  //////////////////////////////////////////////////////////////////////////////
    
  def -(el : (A, Int)) : MultiSet[A] =
    updateMultiplicities(MultiSet.removeMultiplicity(multiplicities, el))

  def --(els : Iterator[(A, Int)]) : MultiSet[A] =
    updateMultiplicities((multiplicities /: els) ((m, el) =>
                                MultiSet.addMultiplicity(m, el)))

  def --(els : Iterable[(A, Int)]) : MultiSet[A] = --(els.iterator)

  def ---(els : Iterator[A]) : MultiSet[A] =
    --(for (el <- els) yield (el, 1))

  def ---(els : Iterable[A]) : MultiSet[A] =
    --(for (el <- els.iterator) yield (el, 1))

  def --(els : MultiSet[A]) : MultiSet[A] = --(els.multiplicities.iterator)

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = multiplicities.toString
}
