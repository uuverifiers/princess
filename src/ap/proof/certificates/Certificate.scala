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

  /**
   * Class for lazily providing the child certificates for a partial certificate
   */
  abstract class CertBuilder {
    def next : Certificate
    def skipNext : Unit
//    def close : Unit

    def skipNext(num : Int) : Unit = {
      var i = 0
      while (i < num) {
        skipNext
        i = i + 1
      }
    }
  }
  
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

  /**
   * Construct a full certificate, by creating the required child certificates
   * on demand. The given functions are supposed to produce either a certificate
   * for a certain subtree, or <code>null</code> in case no certificate exists.
   * The method as a whole will also return <code>null</code> if no complete
   * certificate could be constructed.
   */
  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate

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

  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate =
    certBuilder.next

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
                   !(second.isInstanceOf[PartialCompositionCertificate]) &&
                   second != PartialIdentityCertificate)
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

  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate = {
    val newBuilder = new PartialCertificate.CertBuilder {
      private val firstIt = first.iterator

      def next : Certificate =
        firstIt.next.dfExplore(certBuilder, lemmaBase, 0)

      def skipNext : Unit =
        certBuilder skipNext firstIt.next.arity
    }

    second.dfExplore(newBuilder, lemmaBase, lemmaBaseAssumedInferences)
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

  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate = {
    certBuilder skipNext arity
    result
  }
  
}

/**
 * Partial certificate prepending given inferences to some certificate.
 */
class PartialInferenceCertificate protected[certificates]
                                  (val inferences : BranchInferenceCollection,
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

  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate = {
    val (formulaIt, _) =
      inferences newProvidedFormulas lemmaBaseAssumedInferences

    (lemmaBase assumeFormulas formulaIt) match {
      case Some(cert) => {
        certBuilder.skipNext
println("reusing certificate")
println(cert.assumedFormulas)
        inferences.getCertificate(cert, order)
      }
      case None =>
        certBuilder.next match {
          case null => null
          case sub => inferences.getCertificate(sub, order)
        }
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Partial certificate representing branching proof nodes.
 */
class PartialCombCertificate protected[certificates]
                             (comb : Seq[Certificate] => Certificate,
                              val providedFormulas : Seq[Set[CertFormula]])
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

  def dfExplore(certBuilder : PartialCertificate.CertBuilder,
                lemmaBase : LemmaBase,
                lemmaBaseAssumedInferences : Int) : Certificate = {
    val subRes = new ArrayBuffer[Certificate]
    val providedForsIt = providedFormulas.iterator

    while (providedForsIt.hasNext) {
      val providedFors = providedForsIt.next

      lemmaBase.push
      val sub : Certificate = try {
        (lemmaBase assumeFormulas providedFors.iterator) match {
          case Some(cert) => {
            certBuilder.skipNext
println("reusing certificate")
println(cert.assumedFormulas)
            cert
          }
          case None => {
            val sub = certBuilder.next

            if (sub == null)
              return null

            if (Seqs.disjoint(sub.assumedFormulas, providedFors)) {
println("pruning")
              certBuilder skipNext (arity - subRes.size - 1)
              return sub
            }

            for (cert <- LemmaBase prepareCert sub)
              lemmaBase addCertificate cert

            sub
          }
        }
      } finally {
        lemmaBase.pop
      }

      subRes += sub
    }

    comb(subRes)
  }

}

