/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.PriorityQueue

/**
 * Priority queue that can handle both single elements and pre-sorted sequences
 * (iterators) of elements
 */
class PriorityQueueWithIterators[A](implicit ord: Ordering[A])
      extends PeekIterator[A] {

  private val AC = Debug.AC_QUEUE_WITH_ITERATORS

  private implicit val orderIterator : Ordering[PeekIterator[A]] =
  new Ordering[PeekIterator[A]] {
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
