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

import ap.util.Debug

import scala.collection.mutable.{Set => MSet, HashMap => MHashMap}

object SetTrie {

  private val AC = Debug.AC_BASE_TYPE

}

/**
 * Class for representing sets of sets of totally ordered data elements,
 * implementing a set-trie data-structure.
 */
class SetTrie[T](implicit order : Ordering[T]) extends MSet[Set[T]] {
  import SetTrie._

  private class Node {
    val children = new MHashMap[T, Node]
    var isLast : Boolean = false
    
    def nonEmptyRec : Boolean =
      isLast || children.exists(x => x._2.nonEmptyRec)

    /**
     * Recursively compute the number of sets in this collection.
     */
    def size : Int =
      children.iterator.map(x => x._2.size).sum + (if (isLast) 1 else 0)

    /**
     * Recursively insert a set.
     */
    def insert(el : Iterator[T]) : Unit =
      if (el.hasNext) {
        val head = el.next()
        val child = children.getOrElseUpdate(head, new Node)
        child.insert(el)
      } else {
        isLast = true
      }

    /**
     * Recursively remove a set. Return <code>true</code> if the node
     * does not contain any descendents with flag <code>isLast</code>
     * any more.
     */
    def remove(el : Iterator[T]) : Boolean = {
      if (el.hasNext) {
        val head = el.next()
        for (child <- children get head) {
          if (child.remove(el))
            children -= head
        }
      } else {
        isLast = false
      }

      val res = !isLast && children.isEmpty

      //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
      Debug.assertPost(AC, !res == nonEmptyRec)
      //-END-ASSERTION-////////////////////////////////////////////////////////

      res
    }

    /**
     * Recursively check whether the given set is an element.
     */
    def contains(el : Iterator[T]) : Boolean =
      if (el.hasNext) {
        (children get el.next()) match {
          case Some(child) =>
            child.contains(el)
          case None =>
            false
        }
      } else {
        isLast
      }

    /**
     * Recursively check whether the set-trie contains some
     * (strict or non-strict) subset.
     */
    def containsSubset(el : List[T]) : Boolean =
      isLast || {
        el match {
          case List() =>
            false
          case head :: tail =>
            (children get head) match {
              case Some(child) =>
                child.containsSubset(tail) || containsSubset(tail)
              case None =>
                containsSubset(tail)
            }
        }
      }

    /**
     * Recursively check whether the set-trie contains some
     * (strict or non-strict) super-set.
     */
    def containsSuperset(el : List[T]) : Boolean =
      el match {
        case List() =>
          isLast || children.nonEmpty
        case head :: tail =>
          children.exists {
            case (value, child) =>
              order.compare(value, head) match {
                case n if n < 0 =>
                  child.containsSuperset(el)
                case 0 =>
                  child.containsSuperset(tail)
                case _ =>
                  false
              }
          }
      }

    /**
     * Recursively enumerate the elements of this set-trie.
     */
    def enumerate(prefix : Set[T]) : Iterator[Set[T]] =
      (if (isLast) Iterator(prefix) else Iterator.empty) ++
      (for ((t, child) <- children.iterator;
            el <- child.enumerate(prefix + t)) yield el)
  }

  private val root = new Node

  private def toIterator(el : Set[T]) : Iterator[T] =
    el.toVector.sorted.iterator

  private def toList(el : Set[T]) : List[T] =
    el.toList.sorted

  def clear() : Unit = {
    root.isLast = false
    root.children.clear()
  }

  def addOne(el : Set[T]) : SetTrie.this.type = {
    root.insert(toIterator(el))
    this
  }

  def subtractOne(el : Set[T]) : SetTrie.this.type = {
    root.remove(toIterator(el))
    this
  }

  def contains(el : Set[T]) : Boolean =
    root.contains(toIterator(el))

  /**
   * Check whether the set-trie contains some element that is a
   * (strict or non-strict) subset of the given set.
   */
  def containsSubset(el : Set[T]) : Boolean =
    root.containsSubset(toList(el))

  /**
   * Check whether the set-trie contains some element that is a
   * (strict or non-strict) super-set of the given set.
   */
  def containsSuperset(el : Set[T]) : Boolean =
    root.containsSuperset(toList(el))

  def iterator : Iterator[Set[T]] =
    root.enumerate(Set())

  override def isEmpty : Boolean =
    !root.isLast && root.children.isEmpty

  override def size : Int =
    root.size

}