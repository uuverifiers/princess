/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

object FilterIt {
  
  def apply[T](baseIt : Iterator[T], pred : T => Boolean) : Iterator[T] =
    new FilterIt(baseIt, pred)
  
}

/**
 * An own class for filtering the elements that are returned by an iterator,
 * because the method <code>Iterator.filter</code> is so broken
 */
class FilterIt[T] private (baseIt : Iterator[T],
                           pred : T => Boolean) extends Iterator[T] {
  private var nextVal : T = _
  private var nextValAvailable : Boolean = false

  private def runToNext = {
    while (!nextValAvailable && baseIt.hasNext) {
      nextVal = baseIt.next
      nextValAvailable = pred(nextVal)
    }
  }

  def hasNext = {
    runToNext
    nextValAvailable
  }

  def next = {
    runToNext
    nextValAvailable = false
    nextVal
  }
}
