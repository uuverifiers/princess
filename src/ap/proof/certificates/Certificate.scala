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

import ap.terfor.{TermOrder, SortedWithOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, FilterIt, Seqs}

import scala.collection.mutable.ArrayBuffer

object Certificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
}

/**
 * Datastructures used to express and extract whole, detailed proofs, which can
 * independently be checked and be used for further processing (e.g., to compute
 * interpolants). Certificates are trees/proof terms, with the following class
 * as the abstract superclass of all tree nodes. Proofs are more or less tableau
 * proofs, with rule applications assuming certain formulae on a branch and
 * producing new formulae.
 */
abstract class Certificate {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Certificate.AC,
                   (closingConstraint isSortedBy order) &&
                   size == localProvidedFormulas.size &&
                   (assumedFormulas forall (order isSortingOf _)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * The constraint resulting from this proof
   */
  val closingConstraint : Conjunction
  
  /**
   * Formulae that the proof assumes to be present on this branch (i.e.,
   * premisses of rules applied in the proof). We assume that all formulae
   * live in the antecedent.
   */
  lazy val assumedFormulas : Set[CertFormula] =
    localAssumedFormulas ++
    (for ((cert, providedFormulas) <-
            iterator zip localProvidedFormulas.iterator;
          f <- FilterIt(cert.assumedFormulas.iterator,
                        (f : CertFormula) => !(providedFormulas contains f)))
     yield f)
  
  val localAssumedFormulas : Set[CertFormula]
  
  /**
   * Formulae that are introduced into the antecedent by this rule application
   * (one set for each subproof). This will implicitly simplify formulae (all
   * simplifications that are built into the datastructures are carried out).
   */
  val localProvidedFormulas : Seq[Set[CertFormula]]

  val order : TermOrder

  /**
   * Set of constants occurring in this certificate. By default this will
   * contain the set of all constants in sub-certificates, as well as
   * constants in assumed formulas.
   */
  lazy val constants : Set[ConstantTerm] =
    Seqs.union((for (cert <- subCertificates.iterator)
                yield cert.constants) ++
               (for (f <- localAssumedFormulas.iterator)
                yield f.constants)) -- localBoundConstants

  /**
   * Constants bound by the root operator of the certificate.
   */
  val localBoundConstants : Set[ConstantTerm] = Set()

  def inferenceCount : Int =
    (1 /: this.subCertificates) { case (num, cert) => num + cert.inferenceCount }

  def apply(i : Int) : Certificate
  def length : Int
  def iterator : Iterator [Certificate]
  
  def size = length

  def subCertificates = new IndexedSeq[Certificate] {
    def apply(i : Int) : Certificate = Certificate.this.apply(i)
    def length : Int = Certificate.this.length
    override def iterator = Certificate.this.iterator
  }
  
  def update(newSubCerts : Seq[Certificate]) : Certificate
}

////////////////////////////////////////////////////////////////////////////////

object PartialCertificate {
  
  protected[certificates] val AC = Debug.AC_CERTIFICATES
  
  val IDENTITY = PartialIdentityCertificate

  def apply(inferences : BranchInferenceCollection,
            order : TermOrder) : PartialCertificate =
    if (inferences.inferences.isEmpty)
      IDENTITY
    else
      new PartialInferenceCertificate(inferences, order)
 
  def apply(comb : Seq[Certificate] => Certificate,
            providedFormulas : Seq[Set[CertFormula]]) : PartialCertificate =
    new PartialCombCertificate(comb, providedFormulas)
  
  def apply(comb : Seq[Certificate] => Certificate,
            providedFormulas : Seq[Set[CertFormula]],
            inferences : BranchInferenceCollection,
            order : TermOrder) : PartialCertificate =
    (new PartialCombCertificate(comb,
                                providedFormulas)).andThen(inferences, order)
  
}

/**
 * Class representing a mapping from a vector of certificates to a single
 * new certificate. This is used to handle certificate extraction in branching
 * proofs.
 */
abstract class PartialCertificate {

  val arity : Int

  def apply(subCerts : Seq[Certificate]) : Certificate

  def after(those : Seq[PartialCertificate]) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, this.arity == those.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (those forall (_ == PartialIdentityCertificate))
      this
    else
      PartialCompositionCertificate(those, this)
  }

  def andThen(inferences : BranchInferenceCollection,
              order : TermOrder) : PartialCertificate =
    if (inferences.inferences.isEmpty)
      this
    else
      (new PartialInferenceCertificate(inferences, order)) after List(this)

  /**
   * Bind the first argument of the partial certificate, resulting in a
   * partial certificate with one fewer free arguments, or (in case proof
   * pruning can be performed) a complete certificate
   */
  def bindFirst(cert : Certificate)
               : Either[PartialCertificate, Certificate]

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Partial certificate that represents the identify function.
 */
case object PartialIdentityCertificate extends PartialCertificate {

  val arity : Int = 1

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, subCerts.size == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    subCerts.head
  }

  override def after(those : Seq[PartialCertificate]) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, those.size == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    those.head
  }

  def bindFirst(cert : Certificate) : Either[PartialCertificate, Certificate] =
    Right(cert)

}

/**
 * Composition of a partial certificate and a sequence of partial certificates.
 */
case class PartialCompositionCertificate(first : Seq[PartialCertificate],
                                         second : PartialCertificate)
           extends PartialCertificate {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PartialCertificate.AC,
                   first.size == second.arity && !first.isEmpty &&
                   !(second.isInstanceOf[PartialCompositionCertificate]))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
    
  val arity = (first.iterator map (_.arity)).sum
  
  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, subCerts.size == arity)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val subRes = new ArrayBuffer[Certificate]
    var offset : Int = 0
    for (pc <- first) {
      val newOffset = offset + pc.arity
      subRes += pc(subCerts.slice(offset, newOffset))
      offset = newOffset
    }

    second(subRes)
  }

  override def after(those : Seq[PartialCertificate]) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, those.size == arity)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newFirst = new ArrayBuffer[PartialCertificate]
    var offset : Int = 0
    for (pc <- first) {
      val newOffset = offset + pc.arity
      newFirst += pc after those.slice(offset, newOffset)
      offset = newOffset
    }

    PartialCompositionCertificate(newFirst, second)
  }

  def bindFirst(cert : Certificate) : Either[PartialCertificate, Certificate] = {
    (first.head bindFirst cert) match {
      case Left(pCertFirst) =>
        Left(PartialCompositionCertificate(first.updated(0, pCertFirst), second))
      case Right(certFirst) =>
        (second bindFirst certFirst) match {
          case Left(pCertSecond) =>
            if (first.head.arity > 1)
              Left(PartialCompositionCertificate(first.updated(0,
                     new PartialFixedCertificate(certFirst, first.head.arity - 1)),
                     second))
            else
              Left(PartialCompositionCertificate(first.tail, pCertSecond))
          case x@Right(_) =>
            x
        }
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * A partial certificate with a fixed result.
 */
class PartialFixedCertificate protected[certificates]
                              (result : Certificate,
                               val arity : Int) extends PartialCertificate {

  def apply(subCerts : Seq[Certificate]) : Certificate = result
  
  def bindFirst(cert : Certificate) : Either[PartialCertificate, Certificate] =
    if (arity == 1)
      Right(result)
    else
      Left(new PartialFixedCertificate(result, arity - 1))
  
}

/**
 * Partial certificate prepending given inferences to some certificate.
 */
class PartialInferenceCertificate protected[certificates]
                                  (inferences : BranchInferenceCollection,
                                   order : TermOrder)
      extends PartialCertificate {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PartialCertificate.AC, !inferences.inferences.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val arity : Int = 1

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, subCerts.size == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    inferences.getCertificate(subCerts.head, order)
  }

  def bindFirst(cert : Certificate) : Either[PartialCertificate, Certificate] =
    Right(apply(List(cert)))

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Partial certificate representing branching proof nodes.
 */
class PartialCombCertificate protected[certificates]
                             (comb : Seq[Certificate] => Certificate,
                              providedFormulas : Seq[Set[CertFormula]])
      extends PartialCertificate {

  val arity : Int = providedFormulas.size

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, subCerts.size == arity)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    comb(subCerts)
  }

  def bindFirst(cert : Certificate) : Either[PartialCertificate, Certificate] =
    if (Seqs.disjoint(cert.assumedFormulas, providedFormulas.head))
      // Then the formulas generated by the rule application in the first
      // branch are not actually needed, and we just just take the
      // sub-certificate as certificate altogether
      Right(cert)
    else if (arity == 1)
      Right(comb(List(cert)))
    else
      Left(new PartialCombCertificate(certs => comb(List(cert) ++ certs),
                                      providedFormulas.tail))

}


/**
 * Class to store fragments of certificates. Such fragments can be seen as
 * functions from sequences of certificates (the certificates derived from
 * some subproofs) to certificates. In this sense, every rule application
 * is justified by a partial certificate.
 * 
 * The class also offers the possibility of proof pruning, applied when a 
 * sub-certificate does not actually use any of the formulae generated by a
 * rule application. In this case, instead of applying <code>comb</code> to all
 * sub-certificate, only <code>alt</code> is applied to a selected
 * sub-certificate
 */
/*
class PartialCertificate private (comb : Seq[Certificate] => Certificate,
                                  providedFormulas
                                          : Seq[Option[Set[CertFormula]]],
                                  alt : Certificate => Certificate,
                                  val arity : Int)
      extends ... {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PartialCertificate.AC, providedFormulas.size == arity)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == subCerts.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    comb(subCerts)
  }

  def compose(that : Seq[PartialCertificate]) : PartialCertificate = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == that.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val newArity = (that.iterator map (_.arity)).sum
    
    val newComb = (certs : Seq[Certificate]) => {
      val subRes = new ArrayBuffer[Certificate]
      var offset : Int = 0
      for (pc <- that) {
        val newOffset = offset + pc.arity
        subRes += pc(certs.slice(offset, newOffset))
        offset = newOffset
      }
      apply(subRes)
    }
    
    PartialCertificate(newComb, newArity)
  }
  
  /**
   * Bind the first argument of the partial certificate, resulting in a
   * partial certificate with one fewer free arguments, or (in case proof
   * pruning can be performed) a complete certificate
   */
  def bindFirst(cert : Certificate)
               : Either[PartialCertificate, Certificate] = providedFormulas.head match {
    case Some(fors) if (Seqs.disjoint(cert.assumedFormulas, fors)) =>
      // Then the formulas generated by the rule application in the first
      // branch are not actually needed, and we just just take the
      // sub-certificate as certificate altogether
      Right(alt(cert))
    case _ if (arity == 1) =>
      Right(comb(List(cert))) 
    case _ =>
      Left(new PartialCertificate(certs => comb(List(cert) ++ certs),
                                  providedFormulas.tail,
                                  alt,
                                  arity - 1))
  }
}
*/