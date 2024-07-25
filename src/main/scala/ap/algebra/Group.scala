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

import ap.basetypes.IdealInt
import ap.parser._
import ap.types.Sort
import ap.util.Debug

trait Semigroup {

  /**
   * Domain of the semigroup
   */
  val dom : Sort

  /**
   * Binary operation of the semigroup
   */
  def op(s : ITerm, t : ITerm) : ITerm

  /**
   * <code>num * s</code>, for <code>num > 0</code>
   */
  def times(num : IdealInt, s : ITerm) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_ALGEBRA, num > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    var powers = s
    var res : ITerm = null
    var c = num

    while (c.signum > 0) {
      val (div, mod) = c /% IdealInt(2)

      if (!mod.isZero)
        res = if (res == null) powers else op(res, powers)

      powers = op(powers, powers)
      c = div
    }

    res
  }

  override def toString = dom.toString

}

/**
 * Semigroups that provide a symbolic <code>times</code> operator,
 * which accepts terms as both arguments.
 */
trait SymbolicTimes extends Semigroup {

  /**
   * <code>num * s</code>, where the integer <code>num</code>
   * is symbolically represented by a term.
   */
  def times(num : ITerm, s : ITerm) : ITerm

}

/**
 * Abelian/commutative semigroups
 */
trait Abelian extends Semigroup

/**
 * Monoids are semigroups with a neutral element (or zero)
 */
trait Monoid extends Semigroup {

  /**
   * The neutral element of this monoid
   */
  def identity : ITerm

  /**
   * <code>num * s</code>, for <code>num >= 0</code>
   */
  override def times(num : IdealInt, s : ITerm) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_ALGEBRA, num >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (num.isZero)
      identity
    else
      super.times(num, s)
  }
}

/**
 * Groups are monoids that additionally have inverses
 */
trait Group extends Monoid {

  /**
   * Inverse elements
   */
  def inverse(s : ITerm) : ITerm

  /**
   * <code>num * s</code>
   */
  override def times(num : IdealInt, s : ITerm) : ITerm =
    num.signum match {
      case -1 => inverse(super.times(-num, s))
      case 0  => identity
      case 1  => super.times(num, s)
    }

}
