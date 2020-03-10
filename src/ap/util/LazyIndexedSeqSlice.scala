/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.GenSeq

class LazyIndexedSeqSlice[A](seq : IndexedSeq[A], begin : Int, end : Int)
      extends scala.collection.immutable.IndexedSeq[A] {

  def apply(n : Int) = seq(n + begin)

  def length = end - begin

  override def hashCode() = scala.util.hashing.MurmurHash3.seqHash(this)

  override def equals(that: Any): Boolean = that match {
    case that: GenSeq[_] => (that canEqual this) && (this sameElements that)
    case _               => false
  }

  override def canEqual(that: Any) = true
}
