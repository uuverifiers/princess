/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.algebra

import ap.parser._
import ap.types.Sort
import ap.theories.GroebnerMultiplication

/**
 * The built-in ring of integers
 */
object IntegerRing extends EuclidianRing
                   with    OrderedRing
                   with    CommutativeRing {

  val dom = Sort.Integer
  def int2ring(s : ITerm) = s

  val zero: ITerm = IIntLit(0)
  val one: ITerm  = IIntLit(1)

  def plus(s: ITerm, t: ITerm): ITerm = s +++ t
  def mul (s: ITerm, t: ITerm): ITerm = GroebnerMultiplication.multSimplify(s,t)

  def minus(s: ITerm): ITerm = s.minusSimplify

  def div(s : ITerm, t : ITerm) : ITerm = GroebnerMultiplication.eDiv(s, t)
  def mod(s : ITerm, t : ITerm) : ITerm = GroebnerMultiplication.eMod(s, t)

  def lt (s : ITerm, t : ITerm) : IFormula = (s < t)
  def leq(s : ITerm, t : ITerm) : IFormula = (s <= t)

}
