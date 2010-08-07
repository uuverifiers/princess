/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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