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
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.Debug

object SplitEqCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
}

/**
 * Certificate corresponding to splitting a negated equation into two
 * inequalities.
 */
case class SplitEqCertificate(leftInEq : CertInequality, rightInEq : CertInequality,
                              _leftChild : Certificate, _rightChild : Certificate,
                              _order : TermOrder) extends {
  
  val localAssumedFormulas : Set[CertFormula] = Set({
    implicit val o = _order
    CertNegEquation(rightInEq.lhs + 1)
  })
  
  val localProvidedFormulas : Seq[Set[CertFormula]] =
    Array(Set[CertFormula](leftInEq), Set[CertFormula](rightInEq))
  
} with BinaryCertificate(_leftChild, _rightChild, _order) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(SplitEqCertificate.AC, {
                     implicit val o = _order
                     rightInEq.lhs.isPositive &&
                     leftInEq.lhs + 1 == -(rightInEq.lhs + 1)
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def update(newSubCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(SplitEqCertificate.AC, newSubCerts.size == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val Seq(newLeft, newRight) = newSubCerts
    if ((newLeft eq leftChild) && (newRight eq rightChild))
      this
    else
      copy(_leftChild = newLeft, _rightChild = newRight)
  }

  override def toString : String =
    "SplitEq(" + localAssumedFormulas.head + ", " + leftChild + ", " + rightChild + ")"

}
