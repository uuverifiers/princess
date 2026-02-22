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

package ap.util;

import ap.basetypes.IdealInt

object PlainRange {
  def apply(end : Int) : PlainRange =
    new IntervalPlainRange(0, end)
    
  def apply(start : Int, end : Int) : PlainRange =
    new IntervalPlainRange(start, end)
}

/**
 * Extremely simple class for iterating over intervals of integers
 *
 * TODO: this should be removed
 */
abstract class PlainRange extends Seq[Int]

protected class IntervalPlainRange(start : Int, end : Int) extends PlainRange {

  override def foreach[U](f: Int => U) : Unit = {
    var i : Int = start
    while (i < end) {
      f(i)
      i = i+1
    }
  }
  
  override def filter(pred : Int => Boolean) : PlainRange =
    new PredicatedPlainRange(start, end, pred)
  
  def length = end - start
  
  def iterator = new Iterator[Int] {
    private var i : Int = start
    def hasNext = (i < end)
    def next = {
      val res = i
      i = i+1
      res
    }
  }

  def apply(n : Int) = (n + start)
  
}

protected class PredicatedPlainRange(start : Int, end : Int, pred : Int => Boolean)
      extends IntervalPlainRange(start, end) {

  override def foreach[U](f: Int => U) : Unit = {
    var i : Int = start
    while (i < end) {
      if (pred(i)) f(i)
      i = i+1
    }
  }

  override def filter(pred2 : Int => Boolean) : PlainRange =
    new PredicatedPlainRange(start, end, (i) => pred(i) && pred2(i))

  override def length = throw new UnsupportedOperationException

  override def apply(n : Int) = throw new UnsupportedOperationException
}

////////////////////////////////////////////////////////////////////////////////

object IdealRange {
  def apply(end : IdealInt) : IdealRange =
    new IntervalIdealRange(IdealInt.ZERO, end)
    
  def apply(start : IdealInt, end : IdealInt) : IdealRange =
    new IntervalIdealRange(start, end)
}

/**
 * Extremely simple class for iterating over intervals of integers
 *
 * TODO: this should be removed
 */
abstract class IdealRange extends Seq[IdealInt]

protected class IntervalIdealRange(start : IdealInt,
                                   end : IdealInt) extends IdealRange {

  override def foreach[U](f: IdealInt => U) : Unit = {
    var i : IdealInt = start
    while (i < end) {
      f(i)
      i = i+IdealInt.ONE
    }
  }
  
  override def filter(pred : IdealInt => Boolean) : IdealRange =
    new PredicatedIdealRange(start, end, pred)
  
  def length = (end - start).intValueSafe
  
  def iterator = new Iterator[IdealInt] {
    private var i : IdealInt = start
    def hasNext = (i < end)
    def next = {
      val res = i
      i = i+IdealInt.ONE
      res
    }
  }

  def apply(n : Int) = (start + IdealInt(n))
  
}

protected class PredicatedIdealRange(start : IdealInt, end : IdealInt,
                                     pred : IdealInt => Boolean)
      extends IntervalIdealRange(start, end) {

  override def foreach[U](f: IdealInt => U) : Unit = {
    var i : IdealInt = start
    while (i < end) {
      if (pred(i)) f(i)
      i = i+IdealInt.ONE
    }
  }

  override def filter(pred2 : IdealInt => Boolean) : IdealRange =
    new PredicatedIdealRange(start, end, (i) => pred(i) && pred2(i))

  override def length = throw new UnsupportedOperationException

  override def apply(n : Int) = throw new UnsupportedOperationException
}
