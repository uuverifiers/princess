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

/**
 * Very naive implementation of an LRU cache ... to be improved
 */
class LRUCache[K, V] (maxEntries : Int) {

  private val backend = new scala.collection.mutable.HashMap[K, V]
  
  def get(k : K) : Option[V] = synchronized ( backend get k )
  
  def apply(k : K)(otherwise : => V) : V = (this get k) match {
    case None => {
      val res = otherwise
      this += (k -> res)
      res
    }
    case Some(res) => res
  }
  
  def +=(pair : (K, V)) : Unit = synchronized {
    if (backend.size >= maxEntries) backend.clear
    backend += pair
  }
  
}
