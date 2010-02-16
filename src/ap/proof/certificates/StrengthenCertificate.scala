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

package ap.proof.certificates

import ap.basetypes.IdealInt
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.Debug

object StrengthenCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
}

/**
 * Certificate corresponding to a (possibly repeated) application of the
 * strengthen rule: the inequality <code>weakInEq(0) >= 0</code> is strengthened
 * to the equations <code>weakInEq(0) === 0</code>,
 * <code>weakInEq(0) === 1</code>, etc. and the inequality
 * <code>Set(weakInEq(0) >= eqCases</code>.
 */
case class StrengthenCertificate(weakInEq : InEqConj, eqCases : IdealInt,
                                 children : Seq[Certificate],
                                 order : TermOrder) extends {

  val closingConstraint = {
    implicit val o = order
    conj(for (c <- children.elements) yield c.closingConstraint)
  }
  
  val localAssumedFormulas : Set[Conjunction] = Set(weakInEq)
  
  val localProvidedFormulas : Seq[Set[Conjunction]] = {
    implicit val o = order
    (for (i <- 0 until eqCases.intValueSafe)
       yield Set[Conjunction](weakInEq(0) === i)) ++
      List(Set[Conjunction](weakInEq(0) >= eqCases))
  }
  
} with Certificate {

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(StrengthenCertificate.AC,
                   weakInEq.size == 1 && !weakInEq.isFalse &&
                   eqCases.signum > 0)
  //////////////////////////////////////////////////////////////////////////////

  def length = children.length
  def apply(i : Int) : Certificate = children(i)
  def elements = children.elements

  override def toString : String =
    "Strengthen(" + weakInEq + " -> " + "[" +
    ((for (s <- localProvidedFormulas.elements) yield s.elements.next) mkString ", ") +
    "]" + ", " + (children mkString ", ") + ")"

}
