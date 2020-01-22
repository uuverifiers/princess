/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.collection.mutable.{HashSet => MHashSet}

object UnionSet {
  
  private val AC = Debug.AC_SET_UTILS

  private val ACCESS_CNT_THRESHOLD = 100

  def apply[A](set1 : scala.collection.Set[A],
               set2 : scala.collection.Set[A]) : scala.collection.Set[A] =
/*    if (set1.size == 0)
      set2
    else if (set2.size == 0)
      set1
    else */
      new UnionSet (set1, set2)

  def maybeDuplicateIterator[A](that : scala.collection.Set[A]) = that match {
    case that : UnionSet[A] =>
      that.maybeDuplicateIterator
    case that =>
      that.iterator
  }
}

/**
 * A (lazy) <code>Set</code> that represents the union of two
 * (not necessarily disjoint) <code>Set</code>s
 */
class UnionSet[A] private (set1 : scala.collection.Set[A],
                           set2 : scala.collection.Set[A])
      extends scala.collection.Set[A] {

  def contains(x : A) : Boolean =
    localCopy match {
      case null => {
        maybeCopy
        (set1 contains x) || (set2 contains x)
      }
      case copy =>
        copy contains x
    }
  
  override lazy val size : Int =
    localCopy match {
      case null => {
        var res = set1.size
        for (x <- set2) {
          if (!(set1 contains x))
            res = res + 1
        }
        res
      }
      case copy =>
        copy.size
    }
  
  def iterator : Iterator[A] =
    localCopy match {
      case null => {
        maybeCopy
        set1.iterator ++ FilterIt(set2.iterator, (x:A) => !(set1 contains x))
      }
      case copy =>
        copy.iterator
    }
  
  /**
   * Iterator that might return some of the elements repeatedly
   */
  def maybeDuplicateIterator : Iterator[A] =
    localCopy match {
      case null =>
        UnionSet.maybeDuplicateIterator(set1) ++
          UnionSet.maybeDuplicateIterator(set2)
      case copy =>
        copy.iterator
    }

  def +(elem: A) = throw new UnsupportedOperationException
  def -(elem: A) = throw new UnsupportedOperationException

  private var accessCnt = 0

  private var localCopy : MHashSet[A] = null

  private def maybeCopy : Unit = {
    accessCnt = accessCnt + 1
    if (accessCnt > UnionSet.ACCESS_CNT_THRESHOLD) {
      val copy = new MHashSet[A]
      copy ++= UnionSet.maybeDuplicateIterator(set1)
      copy ++= UnionSet.maybeDuplicateIterator(set2)
      localCopy = copy
    }
  }

}
