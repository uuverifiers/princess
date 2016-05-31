/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates;

import ap.terfor.conjunctions.Conjunction
import ap.terfor.{ConstantTerm, TermOrder}
import ap.util.Debug

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer}
import scala.runtime.ScalaRunTime

object DagCertificateConverter {

  private val AC = Debug.AC_CERTIFICATES

  def apply(cert : Certificate) : Seq[Certificate] = {
    val daggifier = new DagCertificateConverter
    daggifier(cert)
  }

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