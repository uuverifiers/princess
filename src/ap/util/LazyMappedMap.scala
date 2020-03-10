/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

object LazyMappedMap {
  
  private val AC = Debug.AC_MAP_UTILS
  
}

/**
 * Transform a <code>Map m</code> by composing it with two functions into a map
 * <code>valueMapping . m . keyUnmapping</code>. <code>keyMapping</code> has to
 * be the inverse of <code>keyUnmapping</code>, and has to be injective
 */
class LazyMappedMap[A,B,C,D] (oriMap : scala.collection.Map[A,B],
                              keyMapping : (A) => C,
                              keyUnmapping : PartialFunction[C, A],
                              valueMapping : (B) => D)
      extends Map[C,D] {

  def get(key : C) : Option[D] =
    if (keyUnmapping isDefinedAt key) {
      val oriKey = keyUnmapping(key)
      //////////////////////////////////////////////////////////////////////////
      Debug.assertInt(LazyMappedMap.AC, keyMapping(oriKey) == key)
      //////////////////////////////////////////////////////////////////////////
      (oriMap get oriKey) map valueMapping
    } else {
      None
    }
      
  override def size : Int = oriMap.size
  
  def iterator : Iterator[(C,D)] =
    for ((key, value) <- oriMap.iterator) yield {
      val mappedKey = keyMapping(key)
      val mappedValue = valueMapping(value)
      //////////////////////////////////////////////////////////////////////////
      Debug.assertInt(LazyMappedMap.AC, (keyUnmapping isDefinedAt mappedKey) &&
                                        keyUnmapping(mappedKey) == key)
      //////////////////////////////////////////////////////////////////////////      
      (mappedKey, mappedValue)
    }
  
  def removed(key: C) =
    throw new UnsupportedOperationException

  def updated[V1 >: D](key: C, value: V1) =
    throw new UnsupportedOperationException

}
