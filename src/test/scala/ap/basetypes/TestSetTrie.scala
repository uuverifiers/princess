/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.util.{Debug, PlainRange, FilterIt, Logic, Combinatorics}

import scala.collection.mutable.{HashSet => MHashSet}

import org.scalacheck.Properties
import ap.util.Prop._

class TestSetTrie extends Properties("TestSetTrie") {

  Debug.enableAllAssertions(true)

  val values = Vector(1, 2, 3, 4)

  def randomSmallSet =
    (for (v <- values; if Debug.randomBool) yield v).toSet
  val allSets =
    Combinatorics.genSubMultisets(values).map(_.toSet).toVector

  def randomBigSet =
    (for (_ <- 0 until Debug.random(0, 1000)) yield Debug.random(0, 1000)).toSet

  property("testRandomSmall") = {
    for (n <- 0 until 50) {
      val trie = new SetTrie[Int]
      val refSet = new MHashSet[Set[Int]]

      for (k <- 0 until 1000) {
        compareSets(trie, refSet)
        assertTrue("Trie and reference set contain same elements",
                   allSets.forall(s => trie.contains(s) == refSet.contains(s)))
        assertTrue("Trie and reference set contain same subsets",
                   allSets.forall(s => trie.containsSubset(s) ==
                                       refSet.exists(t => t.subsetOf(s))))
        assertTrue("Trie and reference set contain same super-sets",
                   allSets.forall(s => trie.containsSuperset(s) ==
                                       refSet.exists(t => s.subsetOf(t))))

        randomStep(trie, refSet, big = false)
      }
    }

    true
  }

 property("testRandomBig") = {
      val trie = new SetTrie[Int]
      val refSet = new MHashSet[Set[Int]]

      for (k <- 0 until 500) {
        compareSets(trie, refSet)

        val s = randomBigSet
        assertTrue("Trie and reference set contain same elements",
                   trie.contains(s) == refSet.contains(s))
        assertTrue("Trie and reference set contain same subsets",
                   trie.containsSubset(s) ==
                     refSet.exists(t => t.subsetOf(s)))
        assertTrue("Trie and reference set contain same super-sets",
                   trie.containsSuperset(s) ==
                     refSet.exists(t => s.subsetOf(t)))

        randomStep(trie, refSet, big = true)
      }

   true
  }

  def compareSets(trie : SetTrie[Int], refSet : MHashSet[Set[Int]]) = {
        assertTrue("Trie and reference set are equally empty",
                   trie.isEmpty == refSet.isEmpty)
        assertTrue("Trie and reference set have same size",
                   trie.size == refSet.size)
  }

  def randomStep(trie : SetTrie[Int], refSet : MHashSet[Set[Int]], big : Boolean) = {
        val set = if (big) randomBigSet else randomSmallSet
        if (Debug.randomBool) {
          trie += set
          refSet += set
        } else {
          trie -= set
          refSet -= set
        }
  }
}
