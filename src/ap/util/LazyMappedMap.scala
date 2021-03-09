/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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
