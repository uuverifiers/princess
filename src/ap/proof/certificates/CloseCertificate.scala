/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates

import ap.terfor.conjunctions.Conjunction
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.util.Debug

import scala.runtime.ScalaRunTime

object CloseCertificate {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Certificate corresponding to an application of the close rule.
 */
case class CloseCertificate(localAssumedFormulas : Set[CertFormula],
                            order : TermOrder) extends {

  val closingConstraint =
    !conj(for (f <- localAssumedFormulas.iterator) yield f.toConj)(order)
  val localProvidedFormulas = List()
  
} with Certificate {

  def length = 0
  def apply(i : Int) : Certificate = throw new NoSuchElementException
  def iterator = Iterator.empty

  def update(newSubCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(CloseCertificate.AC, newSubCerts.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    this
  }

  override def toString : String =
    "Close(" + (localAssumedFormulas mkString ", ") + ")"

  override val hashCode : Int = ScalaRunTime._hashCode(this)

}
