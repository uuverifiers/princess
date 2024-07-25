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

object LazyMappedSet {
  
  private val AC = Debug.AC_SET_UTILS
  
}

/**
 * Transform a set by applying a given injective function to all of its
 * arguments.
 */
class LazyMappedSet[A,B] (oriSet : scala.collection.Set[A],
                          mapping : (A) => B,
                          unmapping : PartialFunction[B,A])
      extends scala.collection.immutable.Set[B] {

  override def size : Int = oriSet.size
  
  def contains(x : B) : Boolean =
    if (unmapping isDefinedAt x) {
      val oriX = unmapping(x)
      //////////////////////////////////////////////////////////////////////////
      Debug.assertInt(LazyMappedSet.AC, mapping(oriX) == x)
      //////////////////////////////////////////////////////////////////////////
      oriSet contains oriX
    } else {
      false
    }
  
  def iterator : Iterator[B] = for (x <- oriSet.iterator) yield {
    val mappedX = mapping(x)
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertInt(LazyMappedSet.AC, (unmapping isDefinedAt mappedX) &&
                                      unmapping(mappedX) == x)
    ////////////////////////////////////////////////////////////////////////////  
    mappedX
  }
  
  def +(elem: B) = throw new UnsupportedOperationException
  def -(elem: B) = throw new UnsupportedOperationException
}
