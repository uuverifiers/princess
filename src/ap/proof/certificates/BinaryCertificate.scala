/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates

import ap.terfor.TermOrder
import ap.terfor.TerForConvenience._

/**
 * Abstract superclass of certificates with two children
 */
abstract class BinaryCertificate(val leftChild : Certificate,
                                 val rightChild : Certificate,
                                 val order : TermOrder) extends {

  val closingConstraint = {
    implicit val o = order
    leftChild.closingConstraint & rightChild.closingConstraint
  }

} with Certificate {

  def length = 2
  def apply(i : Int) : Certificate = i match {
    case 0 => leftChild
    case 1 => rightChild
    case _ => throw new NoSuchElementException
  }
  def iterator = Array(leftChild, rightChild).iterator

}
