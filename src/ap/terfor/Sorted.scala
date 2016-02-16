/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.terfor;

/**
 * Trait for objects that can be sorted by a <code>TermOrder</code>. It is a
 * design decision that the used order cannot be queried from an object (so that
 * it must not be stored in the object). It can be checked whether an object is
 * consistent with a certain given order, however.
 */
trait Sorted[+T] {
  /**
   * Re-sort an object with a new <code>TermOrder</code>. It is guaranteed that
   * the result <code>isSortedBy(order)</code>
   */
  def sortBy(order : TermOrder) : T
  
  def isSortedBy(order : TermOrder) : Boolean
}
