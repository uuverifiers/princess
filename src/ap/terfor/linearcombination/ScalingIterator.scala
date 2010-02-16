/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.linearcombination;

import ap.basetypes.IdealInt
import ap.util.Debug

object ScalingIterator {
  def apply(coeff : IdealInt, delegate : Iterator[(IdealInt, Term)])
                               : Iterator[(IdealInt, Term)] = delegate match {
    case delegate : ScalingIterator => delegate * coeff
    case _ => coeff match {
                            case IdealInt.ONE => delegate
                            case IdealInt.ZERO => Iterator.empty
                            case _ => new ScalingIterator (coeff, delegate)
    }
  }
}

class ScalingIterator(coeff : IdealInt, delegate : Iterator[(IdealInt, Term)])
                                           extends Iterator[(IdealInt, Term)] {

  def *(newCoeff : IdealInt) = ScalingIterator(coeff * newCoeff, delegate)
  
  def hasNext = delegate.hasNext
  
  def next = {
    val (c, t) = delegate.next
    (c * coeff, t)
  }
  
}
