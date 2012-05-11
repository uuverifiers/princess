/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.basetypes

import ap.util.Debug

object IdealRat {

  private val AC = Debug.AC_BASE_TYPE

  def apply(num : IdealInt, denom : IdealInt) : IdealRat = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealRat.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val g = num gcd denom
    denom.signum match {
      case -1 => new IdealRat(-(num / g), -(denom / g))
      case  1 => new IdealRat(  num / g,    denom / g)
    }
  }
  
}

/**
 * Naive implementation of rational numbers
 */
final class IdealRat private (val num : IdealInt,
                              val denom : IdealInt) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IdealRat.AC,
                   denom.signum > 0 &&
                   (!num.isZero || denom.isOne) &&
                   (num gcd denom).isOne)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

}