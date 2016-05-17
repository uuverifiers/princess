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

import ap.basetypes.IdealInt
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.{Debug, IdealRange}

object OmegaCertificate {
  
  private val AC = Debug.AC_CERTIFICATES

  def strengthenCases(elimConst : ConstantTerm,
                      boundsA : Seq[CertInequality],
                      boundsB : Seq[CertInequality]) : Seq[IdealInt] = {
    val m = IdealInt.max(for (ineq <- boundsB.iterator)
                         yield (ineq.lhs get elimConst).abs)
    for (ineq <- boundsA; coeff = (ineq.lhs get elimConst).abs)
      yield (((m - IdealInt.ONE) * coeff - m) / m + 1)
  }
  
  def providedFormulas(elimConst : ConstantTerm,
                       boundsA : Seq[CertInequality],
                       boundsB : Seq[CertInequality],
                       order : TermOrder,
                       sCases : Seq[IdealInt]) : Seq[Set[CertFormula]] = {
    implicit val o = order

    val darkShadow : Seq[CertInequality] =
      (for ((geq, cases) <- boundsA.iterator zip sCases.iterator;
            geqCoeff = (geq.lhs get elimConst).abs;
            leq <- boundsB.iterator) yield {
         val leqCoeff = (leq.lhs get elimConst).abs
         CertInequality((geq.lhs scale leqCoeff) +
                        (leq.lhs scale geqCoeff) -
                        cases * leqCoeff)
       }).toList
  
    (for ((conj, cases) <- boundsA.iterator zip sCases.iterator;
          i <- IdealRange(cases).iterator)
       yield Set[CertFormula](CertEquation(conj.lhs - i))).toList ++
    List(Set[CertFormula]() ++ darkShadow)
  }

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
                            boundsA : Seq[CertInequality],
                            boundsB : Seq[CertInequality],
                            children : Seq[Certificate],
                            order : TermOrder) extends {

  val closingConstraint = {
    implicit val o = order
    conj(for (c <- children.iterator) yield c.closingConstraint)
  }
  
  val localAssumedFormulas : Set[CertFormula] =
    Set[CertFormula]() ++ boundsA.iterator ++ boundsB.iterator
  
  val strengthenCases : Seq[IdealInt] =
    OmegaCertificate.strengthenCases(elimConst, boundsA, boundsB)

  val localProvidedFormulas : Seq[Set[CertFormula]] =
    OmegaCertificate.providedFormulas(elimConst, boundsA, boundsB,
                                      order, strengthenCases)

} with Certificate {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(OmegaCertificate.AC,
                   (boundsA forall ((conj) =>
                                    (conj.constants contains elimConst) &&
                                    (conj.lhs get elimConst).signum ==
                                      (boundsA(0).lhs get elimConst).signum)) &&
                   (boundsB forall ((conj) =>
                                    (conj.constants contains elimConst) &&
                                    (conj.lhs get elimConst).signum ==
                                      (boundsB(0).lhs get elimConst).signum)) &&
                   (boundsA.isEmpty || boundsB.isEmpty ||
                     (boundsA(0).lhs get elimConst).signum ==
                      -(boundsB(0).lhs get elimConst).signum))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def length = children.length
  def apply(i : Int) : Certificate = children(i)
  def iterator = children.iterator

  def update(newSubCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(OmegaCertificate.AC, newSubCerts.size == children.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (newSubCerts == children) this else copy(children = newSubCerts)
  }

  override def toString : String =
    "Omega(" + elimConst + ", {" +
    ((boundsA.iterator zip strengthenCases.iterator) mkString ", ") + "}, {" +
    (boundsB mkString ", ") + "} -> " + (children mkString ", ") + ")"

}
