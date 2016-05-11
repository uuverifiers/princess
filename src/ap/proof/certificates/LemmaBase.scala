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

package ap.proof.certificates

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object LemmaBase {

  private def randomPick[A](it : Iterator[A]) : A = {
    val x = it.next
    if (it.hasNext && scala.util.Random.nextBoolean)
      randomPick(it)
    else
      x
  }

}

/**
 * Mutable class for managing sets of certificates.
 */
class LemmaBase {

  import LemmaBase._

  private val literals2Certs = new MHashMap[CertFormula, List[Certificate]]
  private var assumedFormulas : Set[CertFormula] = Set()

  def assumeFormula(l : CertFormula) : Option[Certificate] = {
    val oldAssumed = assumedFormulas
    assumedFormulas = assumedFormulas + l

    (literals2Certs get l) match {
      case Some(certs) => {
        literals2Certs -= l

        val it = certs.iterator
        while (it.hasNext) {
          val c = it.next
          if (!registerCertificate(c)) {
            // found a lemma/certificate that proves that the
            // assumed formulas are inconsistent
            assumedFormulas = oldAssumed
            registerCertificate(c)
            for (d <- it)
              registerCertificate(d)
            return Some(c)
          }
        }

        None
      }
      case None =>
        None
    }
  }

  /**
   * Add a certificate to the database. The method returns
   * <code>true</code> if some assumed literal of the certificate
   * is not yet known, false otherwise.
   */
  def addCertificate(cert : Certificate) : Boolean =
    registerCertificate(cert)

  private def registerCertificate(cert : Certificate) : Boolean = {
    val notAssumed =
      for (f <- cert.assumedFormulas.iterator;
           if (!(assumedFormulas contains f)))
      yield f

    if (notAssumed.hasNext) {
      val key = randomPick(notAssumed)
      literals2Certs.put(key, cert :: literals2Certs.getOrElse(key, List()))
      true
    } else {
      false
    }
  }

}