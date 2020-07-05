/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
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
   * <code>num * s</code>, for <code>n > 0</code>
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
   * <code>num * s</code>, for <code>n >= 0</code>
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
