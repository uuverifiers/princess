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
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.TerForConvenience._
import ap.util.{Debug, IdealRange}

import scala.runtime.ScalaRunTime

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

  override val hashCode : Int = ScalaRunTime._hashCode(this)

}
