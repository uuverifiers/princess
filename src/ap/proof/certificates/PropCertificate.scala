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
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object BetaCertificateHelper {
  
  /**
   * Apparently this function cannot be included in BetaCertificate ("illegal
   * cyclic reference"). Compiler bug?
   */
  def providedFormulas(leftFormula : CertFormula, rightFormula : CertFormula) =
    Array(Set(leftFormula), Set(rightFormula, !leftFormula))
  
}

object BetaCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
  /**
   * Convenience method to handle splits with many children
   */
  def apply(children : Seq[(CertFormula, Certificate)],
            order : TermOrder) : BetaCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, children.size >= 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    implicit val o = order
    
    val childrenIt = children.iterator
    childrenIt.next
    childrenIt.next
    
    (BetaCertificate(children(0) _1, children(1) _1,
                     children(0) _2, children(1) _2, order) /: childrenIt) {
       case (cert, (formula, child)) =>
         BetaCertificate(cert.localAssumedFormulas.head, formula, cert, child, order)
    }
  }

  def providedFormulas(leftFormula : CertFormula, rightFormula : CertFormula) =
    BetaCertificateHelper.providedFormulas(leftFormula, rightFormula)
  
}

/**
 * Certificate corresponding to an application of beta rules with lemmas: the
 * rule describes the splitting of an antecedent formula
 * <code>leftFormula | rightFormula</code> into the cases
 * <code>leftFormula</code> and <code>!leftFormula, rightFormula</code>.
 * (In many cases, the formula <code>!leftFormula</code> will not be used in the
 * right branch.)
 */
case class BetaCertificate(leftFormula : CertFormula, rightFormula : CertFormula,
                           _leftChild : Certificate, _rightChild : Certificate,
                           _order : TermOrder) extends {
  
  val localAssumedFormulas = Set[CertFormula]({
    implicit val o = _order
    CertCompoundFormula(leftFormula.toConj | rightFormula.toConj)
  })
  
  val localProvidedFormulas : Seq[Set[CertFormula]] =
    BetaCertificateHelper.providedFormulas(leftFormula, rightFormula)
  
} with BinaryCertificate(_leftChild, _rightChild, _order) {
  
  def update(newSubCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(BetaCertificate.AC, newSubCerts.size == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val Seq(newLeft, newRight) = newSubCerts
    if ((newLeft eq leftChild) && (newRight eq rightChild))
      this
    else
      copy(_leftChild = newLeft, _rightChild = newRight)
  }

  override def toString : String =
    "Beta(" + localAssumedFormulas.head + ", " + leftChild + ", " + rightChild + ")"
  
}
