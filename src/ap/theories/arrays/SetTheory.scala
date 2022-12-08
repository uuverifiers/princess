/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022 Philipp Ruemmer <ph_r@gmx.net>
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

object SetTheory {

  import CombArray.CombinatorSpec
  import IExpression._

  /**
   * Combinators on sets, represented as Boolean-valued
   * arrays. Booleans are represented as numbers <code>{0, 1}</code>,
   * with <code>0</code> representing <code>true</code>.
   */
  def setOps(suffix : String) = Vector(
    CombinatorSpec("union_" + suffix, List(0, 0), 0,
                   (v(2) <= v(0)) & (v(2) <= v(1)) & (v(0) + v(1) <= v(2) + 1)),
    CombinatorSpec("isect_" + suffix, List(0, 0), 0,
                   (v(0) <= v(2)) & (v(1) <= v(2)) & (v(0) + v(1) >= v(2))),
    CombinatorSpec("minus_" + suffix, List(0, 0), 0,
                   (v(0) <= v(2)) & (v(1) + v(2) >= 1) &
                     (v(0) + 1 >= v(1) + v(2))),
    CombinatorSpec("compl_" + suffix, List(0), 0,
                   v(0) + v(1) === 1)
  )

}

/**
 * A theory of combinatorial arrays.
 */
class SetTheory(val elementSort : Sort)
      extends CombArray(Vector(new ExtArray(List(elementSort), Sort.Bool)),
                        SetTheory.setOps(elementSort.name)) {

  val arTheory = subTheories.head
  import arTheory.{select, store, const}

  val sort = arTheory.sort

  /**
   * <code>{}</code>.
   * TODO: turn this into a proper function.
   */
  def emptySet : ITerm = {
    import IExpression._
    const(1)
  }

  /**
   * <code>union(set, {el})</code>.
   * TODO: turn this into a proper function.
   */
  def including(set : ITerm, el : ITerm) : ITerm = {
    import IExpression._
    store(set, el, 0)
  }

  /**
   * <code>{el1, ..., eln}</code>.
   */
  def set(els : ITerm*) : ITerm = {
    import IExpression._
    var res = emptySet
    for (el <- els)
      res = including(res, el)
    res
  }

  /**
   * <code>el in set</code>.
   * TODO: turn this into a proper predicate.
   */
  def contains(set : ITerm, el : ITerm) : IFormula = {
    import IExpression._
    eqZero(select(set, el))
  }

  /**
   * <code>set1</code> is a subset of <code>set2</code>.
   * TODO: turn this into a proper predicate.
   */
  def subsetOf(set1 : ITerm, set2 : ITerm) : IFormula = {
    import IExpression._
    minus(set1, set2) === emptySet
  }

  val Seq(union, isect, minus, compl) = combinators

  override def toString = "SetTheory[" + elementSort + "]"

}
