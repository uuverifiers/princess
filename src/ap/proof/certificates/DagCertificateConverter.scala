/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates;

import ap.basetypes.IdealInt
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{ConstantTerm, TermOrder}
import ap.util.Debug

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer}
import scala.runtime.ScalaRunTime

object DagCertificateConverter {

  private val AC = Debug.AC_CERTIFICATES

  /**
   * Convert the given certificate to a DAG. The resulting vector
   * contains all relevant sub-certificates, with instances of
   * <code>ReferenceCertificate</code> to refer to some certificate
   * in the vector. The root certificate is the last entry of the
   * vector.
   */
  def apply(cert : Certificate) : Seq[Certificate] = {
    val daggifier = new DagCertificateConverter
    daggifier(cert)
  }

  /**
   * Convert an explicit dag certificate back to a normal tree-shaped
   * certificate. Common sub-certificates will still be shared, so
   * no exponential explosion occurs at this point.
   */
  def inline(dagCert : Seq[Certificate]) : Certificate = {
    val inlinedCerts = new Array[Certificate] (dagCert.size)

    def inlineHelp(cert : Certificate) : Certificate = cert match {
      case ReferenceCertificate(id, _, _, _, _) =>
        inlinedCerts(id)
      case cert =>
        cert update (cert.subCertificates map (inlineHelp _))
    }

    for (i <- 0 until dagCert.size)
      inlinedCerts(i) = inlineHelp(dagCert(i))

    inlinedCerts.last
  }

  /**
   * Cumulative size of the certificate.
   */
  def size(dagCert : Seq[Certificate]) : IdealInt =
    (for (c <- dagCert.iterator) yield c.inferenceCount).sum

  /**
   * Certificate representing a sub-proof that is stored at index
   * plus <code>id</code> in the certificate vector.
   */
  case class ReferenceCertificate(id : Int,
                                  localAssumedFormulas : Set[CertFormula],
                                  additionalConstants : Set[ConstantTerm],
                                  closingConstraint : Conjunction,
                                  order : TermOrder) extends {

    val localProvidedFormulas = List()

  } with Certificate {

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(DagCertificateConverter.AC, id >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    def length = 0
    def apply(i : Int) : Certificate = throw new NoSuchElementException
    def iterator = Iterator.empty

    def update(newSubCerts : Seq[Certificate]) : Certificate = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(DagCertificateConverter.AC, newSubCerts.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      this
    }

    override def toString : String = "Ref#" + id

    override val hashCode : Int = ScalaRunTime._hashCode(this)

  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for converting a given certificate to a DAG, by factoring out
 * shared sub-certificates.
 */
class DagCertificateConverter {

  import DagCertificateConverter._

  def apply(cert : Certificate) : Seq[Certificate] = {
    countOccurrences(cert)

    if (certOccurrences exists { case (_, num) => num > 1 }) {
      finalCertificates += daggify(cert)
      finalCertificates
    } else {
      List(cert)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private val certOccurrences =
    new MHashMap[(List[BranchInference], Certificate), Int]

  /**
   * Count how often each sub-certificate occurs in the given certificate.
   */
  private def countOccurrences(cert : Certificate) : Unit = {
    val pair = (List[BranchInference](), cert)

    (certOccurrences get pair) match {

      case Some(num) =>
        certOccurrences.put(pair, num + 1)

      case None => {
        certOccurrences.put(pair, 1)

        // handle individual inferences stored in the certificate
        cert match {
          case BranchInferenceCertificate(infs, child, order) => {
            var remInfs = infs.toList.tail
            while (!remInfs.isEmpty) {
              val subPair = (remInfs, child)
              (certOccurrences get subPair) match {
                case Some(num) => {
                  certOccurrences.put(subPair, num + 1)
                  return
                }
                case None =>
                  certOccurrences.put(subPair, 1)
              }
              remInfs = remInfs.tail
            }
          }
          case _ => // nothing
        }

        for (c <- cert.subCertificates)
          countOccurrences(c)
      }

    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private val certReplacements =
    new MHashMap[(List[BranchInference], Certificate), ReferenceCertificate]

  private var finalCertificates = new ArrayBuffer[Certificate]

  private def addCertReplacement(oldCert : (List[BranchInference], Certificate),
                                 newCert : Certificate) : Certificate = {
    val id = finalCertificates.size
    finalCertificates += newCert

    val refCert = ReferenceCertificate(id,
                                       newCert.assumedFormulas,
                                       newCert.constants,
                                       newCert.closingConstraint,
                                       newCert.order)
    certReplacements.put(oldCert, refCert)

    refCert
  }

  //////////////////////////////////////////////////////////////////////////////

  private def daggify(cert : Certificate) : Certificate = {
    val pair = (List[BranchInference](), cert)
    
    (certReplacements get pair) match {

      case Some(refCert) =>
        refCert

      case None => {
        val newCert = cert match {
          case BranchInferenceCertificate(inf :: remInfs, child, order)
               if (!remInfs.isEmpty) => {
            val (newRemInfs, newChild) = daggify(remInfs, child)
            BranchInferenceCertificate.prepend(inf :: newRemInfs, newChild, order)
          }
          case _ => {
            val newSubCerts = for (c <- cert.subCertificates) yield daggify(c)
            cert update newSubCerts
          }
        }

        if (certOccurrences(pair) > 1 && newCert.inferenceCount > 3)
          addCertReplacement(pair, newCert)
        else
          newCert
      }

    }
  }

  private def daggify(inferences : List[BranchInference], cert : Certificate)
                   : (List[BranchInference], Certificate) = inferences match {

    case List() =>
      (List(), daggify(cert))

    case _ => {
      val pair = (inferences, cert)

      (certReplacements get pair) match {

        case Some(refCert) =>
          (List(), refCert)

        case None => {
          val inf :: remInfs = inferences
          val (newRemInfs, newCert) = daggify(remInfs, cert)
          val newInferences = inf :: newRemInfs

          if (certOccurrences(pair) > 1 &&
              newCert.inferenceCount + newInferences.size > 3) {
            val replCert = BranchInferenceCertificate.prepend(
                             newInferences, newCert, newCert.order)
            (List(), addCertReplacement(pair, replCert))
          } else {
            (newInferences, newCert)
          }
        }

      }
    }
  }

}
