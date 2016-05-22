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

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 ArrayStack}
import ap.util.Debug

object LemmaBase {

  private val AC = Debug.AC_CERTIFICATES

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

  private val assumedFormulaStack = new ArrayStack[Set[CertFormula]]

  private val pendingCertificates = new ArrayBuffer[Certificate]

  def assertAllKnown(fors : Iterable[CertFormula]) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LemmaBase.AC, fors forall assumedFormulas)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  }

  /**
   * Assume the given literal, and return a certificate in case
   * the resulting combination of assumed literals is known to be unsat.
   */
  def assumeFormula(l : CertFormula) : Option[Certificate] = ap.util.Timer.measure("assumeFormula"){
    println("now know: " + l)

    val oldAssumed = assumedFormulas
    assumedFormulas = assumedFormulas + l

    (literals2Certs get l) match {
      case Some(certs) => {
        literals2Certs -= l

        var remCerts = certs
        while (!remCerts.isEmpty) {
          val c = remCerts.head
          if (!registerCertificate(c)) {
            // found a lemma/certificate that proves that the
            // assumed formulas are inconsistent
            assumedFormulas = oldAssumed
            literals2Certs.put(l, remCerts)
            return Some(c)
          }
          remCerts = remCerts.tail
        }

        None
      }
      case None =>
        None
    }
  }

  /**
   * Assume the given literals, and return a certificate in case
   * the resulting combination of assumed literals is known to be unsat.
   */
  def assumeFormulas(ls : Iterator[CertFormula]) : Option[Certificate] = {
    while (ls.hasNext)
      assumeFormula(ls.next) match {
        case None => // nothing
        case x => return x
      }
    None
  }

  def push : Unit = ap.util.Timer.measure("push"){
    println("push " + assumedFormulaStack.size)
    assumedFormulaStack push assumedFormulas
  }

  def pop : Unit = ap.util.Timer.measure("pop"){
    assumedFormulas = assumedFormulaStack.pop
    println("pop " + assumedFormulaStack.size)
//    println(assumedFormulas)

    for (i <- (pendingCertificates.size - 1) to 0 by -1)
      if (registerCertificate(pendingCertificates(i)))
        pendingCertificates remove i
  }

  /**
   * Add a certificate to the database.
   */
  def addCertificate(cert : Certificate) : Unit = ap.util.Timer.measure("addCertificate"){
println("learning certificate")
println(cert.assumedFormulas)
//println(cert)
    if (!registerCertificate(cert))
      pendingCertificates += cert
 }

  /**
   * Add a certificate to the database. The method returns
   * <code>true</code> if some assumed literal of the certificate
   * is not yet known, false otherwise.
   */
  private def registerCertificate(cert : Certificate) : Boolean = {
    val notAssumed =
      for (f <- cert.assumedFormulas.iterator;
           if (!(assumedFormulas contains f)))
      yield f

    if (notAssumed.hasNext) {
      val key = randomPick(notAssumed)
      literals2Certs.put(key, cert :: literals2Certs.getOrElse(key, List()))
println("assigning new watched literal")
      true
    } else {
      false
    }
  }

}