/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

/**
 * Temporary hack to track incompleteness of theory implementations.
 */
object Incompleteness {

  private val flag =
    new scala.util.DynamicVariable[Array[Boolean]] (Array(false))

  flag.value = Array(false)

  def set : Unit = ((flag.value)(0) = true)

  def track[A](comp : => A) : (A, Boolean) = {
    val incomp = Array(false)
    val res = flag.withValue(incomp) {
      comp
    }
    (res, incomp(0))
  }

}