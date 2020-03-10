/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2019-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util

object FastImmutableMap {
  def apply[A, B](m : Map[A, B]) = new FastImmutableMap(m)
  def empty[A, B] = new FastImmutableMap[A, B](Map())
  
  private val AccessBound = 1000
}

/**
 * A double-backed map class that initially stores its elements in a
 * <code>scala.collection.immutable.Map</code>, but copies all data to a
 * <code>scala.collection.mutable.HashMap</code> when many accesses are taking
 * place (since the mutable map enables faster access than the immutable map).
 */
class FastImmutableMap[A, B] private (immMap : Map[A, B])
      extends Map[A, B] {

  import FastImmutableMap.AccessBound

  override def empty = new FastImmutableMap[A, B](Map())

  private var mMap : scala.collection.mutable.HashMap[A, B] = null
  
  private var accessNum = 0

  private def createMMap : Unit = {
    val mm = new scala.collection.mutable.HashMap[A, B]
    mm ++= immMap
    mMap = mm
  }
  
  def get(t : A) : Option[B] = if (mMap == null) {
    accessNum = accessNum + 1
    if (accessNum > AccessBound) {
      createMMap
      mMap get t
    } else {
      immMap get t
    }
  } else {
    mMap get t
  }
  
  override def apply(t : A) : B = if (mMap == null) {
    accessNum = accessNum + 1
    if (accessNum > AccessBound) {
      createMMap
      mMap(t)
    } else {
      immMap(t)
    }
  } else {
    mMap(t)
  }
  
  override def size : Int = immMap.size
  
  def iterator : Iterator[(A, B)] = immMap.iterator
  
  override def + [B1 >: B](kv: (A, B1)) =
    new FastImmutableMap(immMap + kv)
  def updated [B1 >: B](key: A, value : B1) =
    new FastImmutableMap(immMap.updated(key, value))

  override def ++[B1 >: B](xs: scala.collection.GenTraversableOnce[(A, B1)]) =
    new FastImmutableMap(immMap ++ xs)

  def removed(key: A) =
    new FastImmutableMap(immMap - key)

  override def foreach[U](f: ((A, B)) => U): Unit = immMap foreach f

}
