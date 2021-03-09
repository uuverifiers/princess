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

package ap.terfor;

import ap.terfor.preds.Atom

import scala.reflect.ClassTag

object Formula {
  
  /**
   * Check whether the given sequence of formulas contains unsatisfiable
   * elements (in this case, a singleton sequence containing only this element
   * is returned), and otherwise remove all tautologies from it.
   */
  def filterForConj[A <: Formula]
                   (fors : Iterator[A]) : IndexedSeq[A] = {
    if (!fors.hasNext) return IndexedSeq.empty
    
    val nonTrivialFors = Vector.newBuilder[A]
    while (fors.hasNext) {
      val c = fors.next
      if (c.isFalse) return Vector(c)
      if (!c.isTrue) nonTrivialFors += c
    }
    
    nonTrivialFors.result
  }
  
  def conj[A <: Formula : ClassTag]
          (fors : Iterator[A],
           trueFor : A, comb : (IndexedSeq[A]) => A) : A = {
    val nonTrivialFors = filterForConj(fors)
    
    nonTrivialFors.size match {
      case 0 => trueFor
      case 1 => nonTrivialFors(0)
      case _ => comb(nonTrivialFors)
    }
  }
}

abstract class Formula extends TerFor {
  
  /** Return <code>true</code> if this formula is obviously always true */
  def isTrue : Boolean
  
  /** Return <code>true</code> if this formula is obviously always false */
  def isFalse : Boolean
  
  def groundAtoms : Set[Atom]

}
