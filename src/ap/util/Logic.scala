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

object Logic {
  
  def forall(it : Iterator[Boolean]) : Boolean = {
    while (it.hasNext) {
      if (!it.next) return false
    }
    true
  }
  
  def forall(it : Iterable[Boolean]) : Boolean = forall(it.iterator)
  
  def forall(start : Int, end : Int, p : (Int) => Boolean) : Boolean =
    forall(for (i <- PlainRange(start, end).iterator) yield p(i))
  
  def exists(it : Iterator[Boolean]) : Boolean = {
    while (it.hasNext) {
      if (it.next) return true
    }
    false
  }

  def exists(it : Iterable[Boolean]) : Boolean = exists(it.iterator)

  def exists(start : Int, end : Int, p : (Int) => Boolean) : Boolean =
    exists(for (i <- PlainRange(start, end).iterator) yield p(i))

  /**
   * Determines whether <code>true</code> occurs exactly once in the given stream
   */
  def existsOne(it : Iterator[Boolean]) : Boolean = {
    var n : Int = 0
    while (it.hasNext) {
      if (it.next) {
        if (n > 0) return false
        n = n + 1
      }
    }
    n == 1
  }

}
