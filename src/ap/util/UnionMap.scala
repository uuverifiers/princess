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

object UnionMap {
  
  private val AC = Debug.AC_MAP_UTILS

  def apply[A, B](map1 : scala.collection.Map[A, B],
                  map2 : scala.collection.Map[A, B]) : scala.collection.Map[A, B] =
    if (map1.size == 0)
      map2
    else if (map2.size == 0)
      map1
    else
      new UnionMap (map1, map2)

}

/**
 * A (lazy) <code>Map</code> that represents the union of two <code>Map</code>s with
 * disjoint key domains
 */
class UnionMap[A, B] private (map1 : scala.collection.Map[A, B],
                              map2 : scala.collection.Map[A, B])
      extends scala.collection.Map[A, B] {

  def get(t : A) : Option[B] = (map1 get t) match {
    case x@Some(_) => x
    case None => map2 get t
  }
  
  def size : Int = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertInt(UnionMap.AC, Seqs.disjoint(map1.keySet, map2.keySet))
    ////////////////////////////////////////////////////////////////////////////
    map1.size + map2.size
  }
  
  def elements : Iterator[(A, B)] = map1.elements ++ map2.elements
  
}
