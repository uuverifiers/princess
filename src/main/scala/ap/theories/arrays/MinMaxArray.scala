/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.types.Sort
import ap.parser._

object MinMaxArray {

  import CombArray.CombinatorSpec
  import IExpression._

  /**
   * Binary min/max operators on arrays.
   */
  def minMaxOps(suffix : String) = Vector(
    CombinatorSpec("min_" + suffix, List(0, 0), 0,
                   (v(2) <= v(0)) & (v(2) <= v(1)) &
                     ((v(2) === v(0) | (v(2) === v(1))))),
    CombinatorSpec("max_" + suffix, List(0, 0), 0,
                   (v(2) >= v(0)) & (v(2) >= v(1)) &
                     ((v(2) === v(0) | (v(2) === v(1)))))
  )

}

/**
 * Integer-valued arrays with built-in operations for minimum and maximum.
 */
class MinMaxArray(indexSorts : Seq[Sort])
      extends CombArray(Vector(new ExtArray(indexSorts, Sort.Integer)),
                        MinMaxArray.minMaxOps(indexSorts.mkString("-"))) {

  val arTheory = subTheories.head
  import IExpression._

  val sort   = arTheory.sort
  val select = arTheory.select
  val store  = arTheory.store
  val const  = arTheory.const

  /**
   * The maximum element in this array (undefined if there is no maximum).
   */
  def max(ar : ITerm) : ITerm =
    eps({
      val indexVars = indexSorts.zipWithIndex.map { case (s, n) => v(n, s) }
      val cond1 =
        ex(indexSorts,
           select(List(shiftVars(ar, indexVars.size + 1)) ++ indexVars :_*) ===
             v(indexVars.size))
      val cond2 =
        shiftVars(ar, 1) === bin_min(shiftVars(ar, 1), const(v(0)))
      cond1 & cond2
    })

  /**
   * The minimum element in this array (undefined if there is no minimum).
   */
  def min(ar : ITerm) : ITerm =
    eps({
      val indexVars = indexSorts.zipWithIndex.map { case (s, n) => v(n, s) }
      val cond1 =
        ex(indexSorts,
           select(List(shiftVars(ar, indexVars.size + 1)) ++ indexVars :_*) ===
             v(indexVars.size))
      val cond2 =
        shiftVars(ar, 1) === bin_max(shiftVars(ar, 1), const(v(0)))
      cond1 & cond2
    })

  val Seq(bin_min, bin_max) = combinators

  override def toString = "MinMaxArray[" + indexSorts.mkString(", ") + "]"

}
