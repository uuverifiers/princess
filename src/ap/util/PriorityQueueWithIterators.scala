/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.collection.mutable.PriorityQueue

/**
 * Priority queue that can handle both single elements and pre-sorted sequences
 * (iterators) of elements
 */
class PriorityQueueWithIterators[A](implicit ord: Ordering[A])
      extends PeekIterator[A] {

  private val AC = Debug.AC_QUEUE_WITH_ITERATORS

  private implicit val orderIterator = new Ordering[PeekIterator[A]] {
    def compare(thisIt : PeekIterator[A], thatIt : PeekIterator[A]) : Int = {
      ////////////////////////////////////////////////////////////////////////
      Debug.assertInt(AC, thisIt.hasNext && thatIt.hasNext)
      ////////////////////////////////////////////////////////////////////////
      ord.compare(thisIt.peekNext, thatIt.peekNext)
    }
  }

  /** the internal priority queue holding the single elements */
  private val singleElements = new PriorityQueue[A]
  
  /** the internal priority queue holding sequences of elements */
  private val sequences = new PriorityQueue[PeekIterator[A]]

  //////////////////////////////////////////////////////////////////////////////
  
  private var maxElement : A = _
  private var maxElementAvailable : Boolean = false
  
  private def enqueueMaxElement : Unit = {
    if (maxElementAvailable) {
      singleElements += maxElement
      maxElementAvailable = false
    }    
  }
  
  def peekNext : A = {
    if (!maxElementAvailable) {
      def peekNextFromSequence = {
        val maxSeq = sequences.dequeue
        maxElement = maxSeq.next
        if (maxSeq.hasNext) {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, ord.gteq(maxElement, maxSeq.peekNext))
          //-END-ASSERTION-/////////////////////////////////////////////////////
          sequences += maxSeq
        }
      }
      
      if (singleElements.isEmpty) {
        peekNextFromSequence // this throws an exception if the queue
                             // <code>sequences</code> is empty
      } else {
        if (sequences.isEmpty) {
          maxElement = singleElements.dequeue
        } else {
          if (ord.gt(sequences.head.peekNext, singleElements.head)) {
            peekNextFromSequence
          } else {
            maxElement = singleElements.dequeue            
          }
        }        
      }
      
      // only reachable if an element was available (otherwise an exception was
      // thrown)
      maxElementAvailable = true
    }

    maxElement
  }
  
  def next : A = {
    val res = peekNext
    maxElementAvailable = false
    res
  }
  
  def hasNext : Boolean = 
    maxElementAvailable || !singleElements.isEmpty || !sequences.isEmpty
  
  //////////////////////////////////////////////////////////////////////////////
  
  /** Inserts a single element into the priority queue. */
  def +=(elem: A): Unit = {
    enqueueMaxElement
    singleElements += elem
  }

  /** Inserts a sequence as a single element into the priority queue. The
   * given iterator has to produce elements in descending order! */
  def +=(it: Iterator[A]): Unit = {
    if (it.hasNext) {
      enqueueMaxElement
      sequences += PeekIterator(it)
    }
  }

  /** Adds all elements provided by an iterable into the priority queue. */
  def ++=(it: Iterable[A]): Unit = (this ++= it.iterator)

  /** Adds all elements provided by an iterator into the priority queue. */
  def ++=(it: Iterator[A]): Unit = it foreach { e => this += e }
  
  /** Adds all elements to the queue. */
  def enqueue(elems: A*): Unit = (this ++= elems)

  /** Adds all elements to the queue. The
   * given iterators have to produce elements in descending order! */
  def enqueue(it: Iterator[A]): Unit = (this += it)
  
  /** Returns the element with the highest priority in the queue,
   *  and removes this element from the queue.
   *
   *  @throws Predef.NoSuchElementException
   *  @return   the element with the highest priority.
   */
  def dequeue: A = next
  
  /** Returns the element with the highest priority in the queue,
   *  or throws an error if there is no element contained in the queue.
   *
   *  @return   the element with the highest priority.
   */
  def max: A = peekNext
  
  /** Removes all elements from the queue. After this operation is completed,
   *  the queue will be empty.
   */
  def clear(): Unit = {
    maxElementAvailable = false
    singleElements.clear
    sequences.clear
  }
}
