/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof

import ap.terfor.TermOrder

object Vocabulary {
  
  def apply(order : TermOrder) : Vocabulary =
    Vocabulary(order, BindingContext.EMPTY, ConstantFreedom.BOTTOM)
  
  val EMPTY : Vocabulary =
    Vocabulary(TermOrder.EMPTY, BindingContext.EMPTY, ConstantFreedom.BOTTOM) 
  
}

case class Vocabulary (order : TermOrder,
                       bindingContext : BindingContext,
                       constantFreedom : ConstantFreedom) {

  def updateConstantFreedom(cf : ConstantFreedom) : Vocabulary =
    Vocabulary (order, bindingContext, cf)
  
}
