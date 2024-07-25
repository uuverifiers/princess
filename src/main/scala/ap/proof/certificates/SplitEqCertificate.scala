/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates

import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.Debug

import scala.runtime.ScalaRunTime

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

  override val hashCode : Int = ScalaRunTime._hashCode(this)

}
