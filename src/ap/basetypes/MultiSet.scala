/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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
