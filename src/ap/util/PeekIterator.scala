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

object PeekIterator {
  def apply[T](it : Iterator[T]) : PeekIterator[T] = it match {
    case it : PeekIterator[_] => it
    case _ => new PeekIteratorTrafo[T](it)
  }
  
  def single[T](value : T) : PeekIterator[T] = new PeekIterator[T] {
    private var hasnext = true
    def hasNext = hasnext
    def next = {
      hasnext = false
      value
    }
    def peekNext = value
  }
}

class PeekIteratorTrafo[T](delegate : Iterator[T]) extends PeekIterator[T] {
  
  private var nextVal : Option[T] = None
  
  def hasNext = nextVal.isDefined || delegate.hasNext
  
  def next : T = nextVal match {
    case None => delegate.next
    case Some(v) => { nextVal = None; v }
  }
  
  def peekNext : T = nextVal match {
    case None => { val v = delegate.next; nextVal = Some(v); v }
    case Some(v) => v
  }
}

/**
 * Extension of the iterator trait where the next element can be peeked without
 * popping it
 */
trait PeekIterator[+T] extends Iterator[T] {
  def peekNext : T
  
  def dropAll : Unit = {
    while (hasNext) next
  }
}
