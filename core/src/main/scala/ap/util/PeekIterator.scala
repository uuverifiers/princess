/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

object PeekIterator {
  def apply[T](it : Iterator[T]) : PeekIterator[T] = it match {
    case it : PeekIterator[_] => it
    case _ => new PeekIteratorTrafo[T](it)
  }
  
  def single[T](value : T) : PeekIterator[T] = new PeekIterator[T] {
    private var hasnext = true
    def hasNext = hasnext
    def next() = {
      hasnext = false
      value
    }
    def peekNext = value
  }
}

class PeekIteratorTrafo[T](delegate : Iterator[T]) extends PeekIterator[T] {
  
  private var nextVal : Option[T] = None
  
  def hasNext = nextVal.isDefined || delegate.hasNext
  
  def next() : T = nextVal match {
    case None => delegate.next()
    case Some(v) => { nextVal = None; v }
  }
  
  def peekNext : T = nextVal match {
    case None => { val v = delegate.next(); nextVal = Some(v); v }
    case Some(v) => v
  }
}

/**
 * Extension of the iterator trait where the next element can be peeked without
 * popping it
 */
trait PeekIterator[+T] extends Iterator[T] {
  def peekNext : T
  
  def dropAll : Unit = {
    while (hasNext) next()
  }
}
