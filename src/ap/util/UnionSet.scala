/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

  def diff(that : scala.collection.Set[A]) =
    (iterator filterNot that).toSet

}
