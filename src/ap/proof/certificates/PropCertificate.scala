/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.TerForConvenience._
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

import scala.runtime.ScalaRunTime

object BetaCertificateHelper {
  
  /**
   * Apparently this function cannot be included in BetaCertificate ("illegal
   * cyclic reference"). Compiler bug?
   */
  def providedFormulas(leftFormula : CertFormula, rightFormula : CertFormula,
                       lemma : Boolean) =
    Array(Set(leftFormula),
          if (lemma) Set(rightFormula, !leftFormula) else Set(rightFormula))
  
}

object BetaCertificate {
  
  protected[certificates] val AC = Debug.AC_CERTIFICATES
  
  /**
   * Convenience method to handle splits with many children.
   */
  def apply(children : Seq[(CertFormula, Certificate)],
            order : TermOrder) : Certificate =
    naryWithDisjunction(children, order)._2

  /**
   * Convenience method to handle splits with many children. The method will
   * return the new certificate, together with the final formula that was split
   * (the disjunction of the cases provided).
   */
  def naryWithDisjunction(
            children : Seq[(CertFormula, Certificate)],
            order : TermOrder) : (CertFormula, Certificate) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, !children.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    naryHelp(children.toIndexedSeq, 0, children.size, order)
  }

  private def naryHelp(children : IndexedSeq[(CertFormula, Certificate)],
                       begin : Int, end : Int,
                       order : TermOrder) : (CertFormula, Certificate) =
    if (end == begin + 1) {
      children(begin)
    } else {
      val mid = (begin + end) / 2
      val (leftFor, leftCert) = naryHelp(children, begin, mid, order)
      val (rightFor, rightCert) = naryHelp(children, mid, end, order)
      val res = betaIfNeeded(leftFor, rightFor, false,
                             leftCert, rightCert, order)
      if (res eq leftCert)
        (leftFor, leftCert)
      else if (res eq rightCert)
        (rightFor, rightCert)
      else
        (res.localAssumedFormulas.head, res)
    }

  /**
   * Create a beta certificate, but handle the case that one of the
   * disjuncts subsumes the other; in this case, simply one of the child
   * certificates will be returned.
   */
  def betaIfNeeded(leftFormula : CertFormula, rightFormula : CertFormula,
                   lemma : Boolean,
                   leftChild : Certificate, rightChild : Certificate,
                   order : TermOrder) : Certificate =
    (leftFormula, rightFormula) match {
      case (leftFormula : CertArithLiteral,
            rightFormula : CertArithLiteral) => {
        implicit val o = order

        val leftConj = leftFormula.toConj
        val rightConj = rightFormula.toConj
        val disj = leftConj | rightConj
        
        if (disj == leftConj)
          leftChild
        else if (disj == rightConj)
          rightChild
        else
          BetaCertificate(leftFormula, rightFormula, lemma,
                          leftChild, rightChild, order)
      }
      case (leftFormula, rightFormula) if leftFormula == rightFormula =>
        leftChild
      case _ =>
        BetaCertificate(leftFormula, rightFormula, lemma,
                        leftChild, rightChild, order)
    }

  def providedFormulas(leftFormula : CertFormula, rightFormula : CertFormula,
                       lemma : Boolean) =
    BetaCertificateHelper.providedFormulas(leftFormula, rightFormula, lemma)
  
}

/**
 * Certificate corresponding to an application of beta rules with lemmas: the
 * rule describes the splitting of an antecedent formula
 * <code>leftFormula | rightFormula</code> into the cases
 * <code>leftFormula</code> and <code>!leftFormula, rightFormula</code>.
 * (If <code>lemma</code> is not set, the second case is just
 * <code>rightFormula</code>)
 */
case class BetaCertificate(leftFormula : CertFormula, rightFormula : CertFormula,
                           lemma : Boolean,
                           _leftChild : Certificate, _rightChild : Certificate,
                           _order : TermOrder) extends {
  
  val localAssumedFormulas = Set[CertFormula]({
    implicit val o = _order
    val disj = leftFormula.toConj | rightFormula.toConj
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(BetaCertificate.AC, !disj.isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    CertCompoundFormula(disj)
  })
  
  val localProvidedFormulas : Seq[Set[CertFormula]] =
    BetaCertificateHelper.providedFormulas(leftFormula, rightFormula, lemma)
  
} with BinaryCertificate(_leftChild, _rightChild, _order) {
  
  def update(newSubCerts : Seq[Certificate]) : Certificate =
    update(newSubCerts, lemma)

  def update(newSubCerts : Seq[Certificate], newLemma : Boolean) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaCertificate.AC, newSubCerts.size == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val Seq(newLeft, newRight) = newSubCerts
    if ((newLeft eq leftChild) && (newRight eq rightChild) && (lemma == newLemma))
      this
    else
      copy(_leftChild = newLeft, _rightChild = newRight, lemma = newLemma)
  }

  override def toString : String =
    "Beta(" + localAssumedFormulas.head + ", " + leftChild + ", " + rightChild + ")"
  
  override val hashCode : Int = ScalaRunTime._hashCode(this)

}
