/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2021 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.basetypes

import scala.collection.mutable.{HashMap => MHashMap}

/**
 * A simple, textbook implementation of a union-find data structure.
 */
class UnionFind[D] extends Cloneable {
  private val parent = new MHashMap[D, D]
  private val rank   = new MHashMap[D, Int]

  /**
   * Find the representing element for <code>d</code>. Two
   * elements belong to the same set iff they have the same
   * representative.
   */
  def apply(d : D) : D = {
    val p = parent(d)
    if (p == d) {
      p
    } else {
      val res = apply(p)
      parent.put(d, res)
      res
    }
  }

  /**
   * Check whether an element is already present in the forest.
   */
  def contains(d : D) : Boolean =
    parent contains d

  /**
   * Add a new element to the forest.
   */
  def makeSet(d : D) : Unit = {
    parent.put(d, d)
    rank.put(d, 0)
  }

  /**
   * Add a new element to the forest; the operation has no effect
   * if the element is already present in the forest.
   */
  def makeSetIfNew(d : D) : Unit = if (!contains(d)) makeSet(d)

  /**
   * Iterator over all elements of this forest.
   */
  def elements : Iterator[D] = parent.keysIterator

  /**
   * Join two sets.
   */
  def union(d : D, e : D) : Unit = {
    val dp = apply(d)
    val ep = apply(e)
      
    if (dp != ep) {
      val dr = rank(dp)
      val er = rank(ep)
      if (dr < er) {
        parent.put(dp, ep)
      } else if (dr > er) {
        parent.put(ep, dp)
      } else {
        parent.put(ep, dp)
        rank.put(dp, dr + 1)
      }
    }
  }

  override def clone : UnionFind[D] = {
    val res = new UnionFind[D]
    res.parent ++= this.parent
    res.rank ++= this.rank
    res
  }

  override def toString : String = parent.toString
}
