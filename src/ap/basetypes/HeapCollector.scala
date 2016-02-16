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

package ap.basetypes;

object HeapCollector {
  
  class None[T] extends HeapCollector[T, None[T]] {
    def +(element : T, otherData : None[T]) : None[T] = this    
  }
  
  def NONE[T] = new None[T]
  
}

/**
 * A general interface for collecting informations about elements stored in a
 * heap (in particular, in a <code>LeftistHeap</code>). This class can be seen
 * as a monomoid morphism, mapping a heap (seen as a multiset or monoid) to
 * something else.
 */
trait HeapCollector[-T, HC] {

  def +(element : T, otherData : HC) : HC
  
}
