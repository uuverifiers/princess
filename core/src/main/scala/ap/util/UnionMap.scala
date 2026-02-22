/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

object UnionMap {
  
  private val AC = Debug.AC_MAP_UTILS

  def apply[A, B](map1 : scala.collection.Map[A, B],
                  map2 : scala.collection.Map[A, B])
                 : scala.collection.Map[A, B] =
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
      extends scala.collection.immutable.Map[A, B] {

  def get(t : A) : Option[B] = (map1 get t) match {
    case x@Some(_) => x
    case None => map2 get t
  }
  
  override def size : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(UnionMap.AC, Seqs.disjoint(map1.keySet, map2.keySet))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    map1.size + map2.size
  }
  
  def iterator : Iterator[(A, B)] = map1.iterator ++ map2.iterator
  
  def + [B1 >: B](kv: (A, B1)) = throw new UnsupportedOperationException
  def -(key: A) = throw new UnsupportedOperationException

}
