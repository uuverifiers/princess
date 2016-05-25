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
                                 ArrayStack, HashSet => MHashSet}

import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object LemmaBase {

  private val AC = Debug.AC_CERTIFICATES

  def prepareCert(cert : Certificate) : Option[Certificate] = {
    if (isReuseMarked(cert))
      return None

    val simp = cert match {
      case BranchInferenceCertificate(inferences, child, order) => {
        val simpInfs = inferences dropWhile {
          case _ : AlphaInference |
               _ : ReduceInference |
               _ : ReducePredInference |
               _ : CombineEquationsInference |
               _ : CombineInequalitiesInference |
               _ : SimpInference |
               _ : AntiSymmetryInference |
               _ : DirectStrengthenInference => true
          case _ => false
        }
        BranchInferenceCertificate.prepend(simpInfs, child, order)
      }
      case cert => cert
    }

    if (isNonTrivial(simp))
      Some(BranchInferenceCertificate.prepend(List(ReusedProofMarker),
                                              simp, simp.order))
    else
      None
  }

  private def isReuseMarked(cert : Certificate) : Boolean = cert match {
    case BranchInferenceCertificate(inferences, child, order) =>
      inferences contains ReusedProofMarker
    case _ => false
  }

  private def isNonTrivial(cert : Certificate) : Boolean = cert match {
    case BranchInferenceCertificate(Seq(ReusedProofMarker), child, _) =>
      isNonTrivial(child)
    case _ : BranchInferenceCertificate =>
      true
    case _ : CloseCertificate =>
      false
    case _ =>
      true
  }

  private class LemmaRecord(val cert : Certificate,
                            val watchable : Seq[CertFormula],
                            val id : Int) {
    var reuseCounter = 0

    def printWatchable : Unit = {
      print("[")
      print(watchable mkString ",\n ")
      println("]")
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Mutable class for managing sets of certificates.
 */
class LemmaBase {

  import LemmaBase._

  // Mapping from watched formulas to lemmas/certificates
  private val literals2Certs = new MHashMap[CertFormula, List[LemmaRecord]]

  // Formulas that have been asserted on decision level 0
  private val assumedFormulasL0 = new MHashSet[CertFormula]
  // Formulas that have currently been asserted on levels >0
  private var assumedFormulas : Set[CertFormula] = Set()

  // Stack for <code>assumedFormulas</code>
  private val assumedFormulaStack = new ArrayStack[Set[CertFormula]]

  // Certificates that have been added, but can currently not
  // be put in <code>literals2Certs</code> since they are in conflict
  // with asserted formulas
  private val pendingCertificates = new ArrayBuffer[LemmaRecord]

  private var certNum = 0

  def allKnown(fors : Iterable[CertFormula]) : Boolean =
    fors forall { x => assumedFormulasL0(x) || assumedFormulas(x) }

  /**
   * Assume the given literal, and return a certificate in case
   * the resulting combination of assumed literals is known to be unsat.
   */
  def assumeFormula(l : CertFormula) : Option[Certificate] = ap.util.Timer.measure("assumeFormula"){
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LemmaBase.AC, pendingCertificates.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (assumedFormulasL0 contains l)
      return None

    if (assumedFormulaStack.isEmpty) {
      assumedFormulasL0 += l
println("now know on L0 (" + assumedFormulasL0.size + "): " + l)

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      // at the moment we assume that no L0 formulas are added after
      // finding certificates
      Debug.assertInt(LemmaBase.AC, literals2Certs.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      None
    } else {
      val oldAssumed = assumedFormulas
      assumedFormulas = assumedFormulas + l
println("now know (" + assumedFormulas.size + "): " + l)

      (literals2Certs get l) match {
        case Some(certs) => {
          literals2Certs -= l

          var remCerts = certs
          while (!remCerts.isEmpty) {
            val c = remCerts.head
            if (!registerCertificate(c)) {
              // found a lemma/certificate that proves that the
              // assumed formulas are inconsistent
println("matching certificate #" + c.id)
              assumedFormulas = oldAssumed
              literals2Certs.put(l, remCerts)
              return Some(c.cert)
            }
            remCerts = remCerts.tail
          }

          None
        }
        case None =>
          None
      }
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

  /**
   * Pop a frame of the assertion stack. If the assumed formulas after
   * pop are still inconsistent with some stored certificate, such a certificate
   * is returned.
   */
  def pop : Option[Certificate] = ap.util.Timer.measure("pop"){
    assumedFormulas = assumedFormulaStack.pop
    println("pop " + assumedFormulaStack.size)
//    println(assumedFormulas)

    var i = pendingCertificates.size
    while (i > 0) {
      i = i - 1
      if (registerCertificate(pendingCertificates(i)))
        pendingCertificates remove i
      else
        return Some(pendingCertificates(i).cert)
    }

    None
  }

  /**
   * Add a certificate to the database.
   */
  def addCertificate(cert : Certificate) : Unit = ap.util.Timer.measure("addCertificate"){

println("learning certificate #" + certNum)

    val order = cert.order
    implicit val ordering = new Ordering[CertFormula] {
      def compare(a : CertFormula, b : CertFormula) =
        Conjunction.compare(a.toConj, b.toConj, order)
    }

    val watchable =
      (cert.assumedFormulas filterNot assumedFormulasL0).toIndexedSeq.sorted

    val record = new LemmaRecord(cert, watchable, certNum)
    certNum = certNum + 1

println("watchable (" + watchable.size + "/" + cert.assumedFormulas.size + ")")
record.printWatchable

    if (!registerCertificate(record))
      pendingCertificates += record
  }

  /**
   * Add a certificate to the database. The method returns
   * <code>true</code> if some assumed literal of the certificate
   * is not yet known, false otherwise.
   */
  private def registerCertificate(record : LemmaRecord) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LemmaBase.AC, !(record.watchable exists assumedFormulasL0))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val notAssumed =
      for (f <- record.watchable.iterator; if (!(assumedFormulas contains f)))
      yield f

    if (notAssumed.hasNext) {
      val key = randomPick(notAssumed)
      literals2Certs.put(key, record :: literals2Certs.getOrElse(key, List()))
println("assigning new watched literal")
      true
    } else {
      false
    }
  }

  private val rand = new scala.util.Random

  private def randomPick[A](it : Iterator[A]) : A = {
    val x = it.next
    if (it.hasNext && rand.nextBoolean)
      randomPick(it)
    else
      x
  }
}