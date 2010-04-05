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
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.Debug

object OmegaCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
}

/**
 * Certificate corresponding to an application of the Omega rule, which has the
 * same effect as repeated application of Strengthen to the inequalities
 * <code>boundsA</code> in a goal.
 * 
 * For each of the inequalities in <code>boundsA</code>,
 * <code>strengthenCases</code> tells how often
 * Strengthen is applied. The counting works just like in
 * <code>StrengthenCertificate</code>, i.e., <code>1</code> means that
 * Strenghten is applied once (and there are two cases). 
 */
case class OmegaCertificate(elimConst : ConstantTerm,
                            boundsA : Seq[InEqConj], boundsB : Seq[InEqConj],
                            children : Seq[Certificate],
                            order : TermOrder) extends {

  val closingConstraint = {
    implicit val o = order
    conj(for (c <- children.elements) yield c.closingConstraint)
  }
  
  val localAssumedFormulas : Set[Conjunction] =
    Set() ++ (for (c <- boundsA.elements ++ boundsB.elements) yield inEqConj2Conj(c))
  
  val strengthenCases = {
    val m =
      IdealInt.max(for (conj <- boundsB.elements) yield (conj(0) get elimConst).abs)
    for (conj <- boundsA; val coeff = (conj(0) get elimConst).abs)
      yield (((m - IdealInt.ONE) * coeff - m) / m + 1)
  }

  val darkShadow : Seq[InEqConj] = {
    implicit val o = order
    (for ((geq, cases) <- boundsA.elements zip strengthenCases.elements;
          val geqCoeff = (geq(0) get elimConst).abs;
          leq <- boundsB.elements) yield {
       val leqCoeff = (leq(0) get elimConst).abs
       leqCoeff * geq(0) + geqCoeff * leq(0) - cases * leqCoeff >= 0
     }).toList
  }
  
  val localProvidedFormulas : Seq[Set[Conjunction]] = {
    implicit val o = order
    (for ((conj, cases) <- boundsA.elements zip strengthenCases.elements;
         i <- (0 until cases.intValueSafe).elements)
       yield Set[Conjunction](conj(0) === i)).toList ++
    List(Set() ++ (for (c <- darkShadow) yield inEqConj2Conj(c)))
  }

} with Certificate {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(OmegaCertificate.AC,
                   (boundsA forall ((conj) => conj.size == 1 &&
                                    (conj.constants contains elimConst) &&
                                    (conj(0) get elimConst).signum ==
                                      (boundsA(0)(0) get elimConst).signum)) &&
                   (boundsB forall ((conj) => conj.size == 1 &&
                                    (conj.constants contains elimConst) &&
                                    (conj(0) get elimConst).signum ==
                                      (boundsB(0)(0) get elimConst).signum)) &&
                   (boundsA.isEmpty || boundsB.isEmpty ||
                     (boundsA(0)(0) get elimConst).signum ==
                      -(boundsB(0)(0) get elimConst).signum))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def length = children.length
  def apply(i : Int) : Certificate = children(i)
  def elements = children.elements

  override def toString : String =
    "Omega(" + elimConst + ", {" +
    ((boundsA.elements zip strengthenCases.elements) mkString ", ") + "}, {" +
    (boundsB mkString ", ") + "} -> " + (children mkString ", ") + ")"

}
