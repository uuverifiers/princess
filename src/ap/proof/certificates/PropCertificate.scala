/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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
