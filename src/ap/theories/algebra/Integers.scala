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

package ap.theories.algebra

import ap.parser._
import ap.types.Sort
import ap.theories.GroebnerMultiplication

/**
 * The built-in ring of integers
 */
object IntegerRing extends Ring {

  val dom = Sort.Integer
  def int2ring(s : ITerm) = s

  def zero : ITerm = IIntLit(0)
  def one: ITerm   = IIntLit(1)

  def plus(s: ITerm, t: ITerm): ITerm = s + t
  def mul (s: ITerm, t: ITerm): ITerm = GroebnerMultiplication.mult(s, t)

  def minus(s: ITerm): ITerm = -s

}
