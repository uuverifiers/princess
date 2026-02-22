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

import ap.basetypes.IdealInt
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.TerForConvenience._
import ap.util.{Debug, IdealRange}

import scala.runtime.ScalaRunTime

object StrengthenCertificateHelper {
  
  def providedFormulas(weakInEq : CertInequality, eqCases : IdealInt,
                       order : TermOrder) = {
    implicit val o = order
    (for (i <- IdealRange(eqCases))
       yield Set[CertFormula](CertEquation(weakInEq.lhs - i))) ++
      List(Set[CertFormula](CertInequality(weakInEq.lhs - eqCases)))
  }
  
}

object StrengthenCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
  def providedFormulas(weakInEq : CertInequality, eqCases : IdealInt,
                       order : TermOrder) =
    StrengthenCertificateHelper.providedFormulas(weakInEq, eqCases, order)
    
}

/**
 * Certificate corresponding to a (possibly repeated) application of the
 * strengthen rule: the inequality <code>weakInEq(0) >= 0</code> is strengthened
 * to the equations <code>weakInEq(0) === 0</code>,
 * <code>weakInEq(0) === 1</code>, etc. and the inequality
 * <code>weakInEq(0) >= eqCases</code>.
 */
case class StrengthenCertificate(weakInEq : CertInequality, eqCases : IdealInt,
                                 children : Seq[Certificate],
                                 order : TermOrder) extends {

  val closingConstraint = {
    implicit val o = order
    conj(for (c <- children.iterator) yield c.closingConstraint)
  }
  
  val localAssumedFormulas : Set[CertFormula] = Set(weakInEq)
  
  val localProvidedFormulas : Seq[Set[CertFormula]] =
    StrengthenCertificateHelper.providedFormulas(weakInEq, eqCases, order)
  
} with Certificate {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(StrengthenCertificate.AC,
                   !weakInEq.isFalse && eqCases.signum > 0)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def length = children.length
  def apply(i : Int) : Certificate = children(i)
  def iterator = children.iterator

  def update(newSubCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(StrengthenCertificate.AC, newSubCerts.size == children.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (newSubCerts == children) this else copy(children = newSubCerts)
  }

  override def toString : String =
    "Strengthen(" + weakInEq + " -> " + "[" +
    ((for (s <- localProvidedFormulas.iterator) yield s.head) mkString ", ") +
    "]" + ", " + (children mkString ", ") + ")"

  override val hashCode : Int = ScalaRunTime._hashCode(this)

}
