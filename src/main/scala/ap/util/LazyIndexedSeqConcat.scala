/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2019-2020 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.util;

import scala.collection.GenSeq

object LazyIndexedSeqConcat {

  def apply[A](a : IndexedSeq[A], b : IndexedSeq[A]) : IndexedSeq[A] =
    if (a.isEmpty)
      b
    else if (b.isEmpty)
      a
    else
      new LazyIndexedSeqConcat(a, b)

}

class LazyIndexedSeqConcat[A](a : IndexedSeq[A], b : IndexedSeq[A])
      extends scala.collection.immutable.IndexedSeq[A] {

  private val aSize = a.size
  private val bSize = b.size

  def apply(n : Int) = if (n < aSize) a(n) else b(n - aSize)

  def length = aSize + bSize

  override def iterator : Iterator[A] = a.iterator ++ b.iterator

  override def foreach[U](f: A => U) : Unit = {
    a foreach f
    b foreach f
  }

  override def hashCode() = scala.util.hashing.MurmurHash3.seqHash(this)

  override def equals(that: Any): Boolean = that match {
    case that: GenSeq[_] => (that canEqual this) && (this sameElements that)
    case _               => false
  }

  override def canEqual(that: Any) = true
}
