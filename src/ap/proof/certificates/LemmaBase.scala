/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2022 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 ArrayStack, HashSet => MHashSet}
import scala.util.Sorting

import ap.terfor.conjunctions.Conjunction
import ap.terfor.ConstantTerm
import ap.util.{Debug, Seqs}

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

  // Obsolete constants; certificates containing those constants
  // should no longer be used
  private val obsoleteConstants = new MHashSet[ConstantTerm]

  private var certNum = 0

  /**
   * Check whether all of the given formulas have been asserted.
   */
  def allKnown(fors : Iterable[CertFormula]) : Boolean =
    fors forall { x => assumedFormulasL0(x) || assumedFormulas(x) }

  /**
   * Check whether all of the given formulas have been asserted;
   * if not, return some formula that was not asserted
   */
  def allKnownWitness(fors : Iterable[CertFormula]) : Option[CertFormula] = {
    for (x <- fors)
      if (!(assumedFormulasL0(x) || assumedFormulas(x)))
        return Some(x)
    None
  }

  /**
   * Assume the given literal, and return a certificate in case
   * the resulting combination of assumed literals is known to be unsat.
   */
  def assumeFormula(l : CertFormula) : Option[Certificate] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LemmaBase.AC, pendingCertificates.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (assumedFormulasL0 contains l) {
      None
    } else if (assumedFormulaStack.isEmpty) {
      assumedFormulasL0 += l
//println("now know on L0 (" + assumedFormulasL0.size + "): " + l)

      updateWatchedLiteral(l) match {
        case null =>
          None
        case record => {
          // then the lemma base is in an inconsistent state and cannot
          // be used anymore (for the time being); record this by adding
          // the certificate as pending
          pendingCertificates += record
          Some(record.cert)
        }
      }

    } else {
      val oldAssumed = assumedFormulas
      assumedFormulas = assumedFormulas + l

      if (oldAssumed eq assumedFormulas) {
        None
      } else {
//println("now know (" + assumedFormulas.size + "): " + l)
        updateWatchedLiteral(l) match {
          case null =>
            None
          case record => {
            // then the assumed literal has to be removed again
            assumedFormulas = oldAssumed
            Some(record.cert)
          }
        }
      }
    }
  }

  /**
   * Check whether the given formula is watched in any certificates;
   * if you, find new watched literals. The method might return a certificate
   * that shows that the assumed formulas are inconsistent, otherwise
   * <code>null</code>.
   */
  private def updateWatchedLiteral(l : CertFormula) : LemmaRecord = {
    val res = (literals2Certs get l) match {
      case Some(certs) => {
        literals2Certs -= l

        var remCerts = certs
        var res : LemmaRecord = null

        while (!remCerts.isEmpty) {
          val c = remCerts.head
          watchCertificate(c) match {
            case null =>
              remCerts = remCerts.tail
            case updatedC => {
              // found a lemma/certificate that proves that the
              // assumed formulas are inconsistent

//println("matching certificate #" + updatedC.id)

              val newRemCerts =
                if (c eq updatedC) remCerts else (updatedC :: remCerts.tail)
              literals2Certs.put(l, newRemCerts)

              res = updatedC
              remCerts = List()
            }
          }
        }

        res
      }

      case None =>
        null
    }

      /*
      // naive test, whether any lemma can be applied
      try {
        import ap.terfor.conjunctions.ReduceWithConjunction
        val allAssumptions =
          Conjunction.conj(
          (for (f <- assumedFormulasL0.iterator;
                if (!f.isInstanceOf[CertCompoundFormula]))
           yield f.toConj) ++
          (for (f <- assumedFormulas.iterator;
                if (!f.isInstanceOf[CertCompoundFormula]))
           yield f.toConj),
          l.order)

        if (!allAssumptions.isFalse) {
          val reducer = ReduceWithConjunction(allAssumptions, l.order)

          for ((_, certs) <- literals2Certs; cert <- certs)
            if (cert.watchable forall { f => reducer(f.toConj).isTrue }) {
              println("applicable certificate #" + cert.id + ": ")
              cert.printWatchable
            }
        }

      } catch {
        case _ : Throwable => // ignore, since the considered orders
                              // might not always be correct, which can
                              // lead to exceptions
      }
      */

    res
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

  def push : Unit = {
//println("push " + assumedFormulaStack.size)
    assumedFormulaStack push assumedFormulas
  }

  /**
   * Pop a frame of the assertion stack. If the assumed formulas after
   * pop are still inconsistent with some stored certificate, such a certificate
   * is returned.
   */
  def pop : Option[Certificate] = {
    assumedFormulas = assumedFormulaStack.pop
//println("pop " + assumedFormulaStack.size)

    var i = pendingCertificates.size
    while (i > 0) {
      i = i - 1
      val pendingCert = watchCertificate(pendingCertificates(i))
      if (pendingCert == null) {
        pendingCertificates remove i
      } else {
        pendingCertificates(i) = pendingCert
        return Some(pendingCert.cert)
      }
    }

    None
  }

  def hasEmptyStack : Boolean = assumedFormulaStack.isEmpty

  /**
   * Add a certificate to the database.
   */
  def addCertificate(cert : Certificate) : Unit = {
//println("learning certificate #" + certNum)

    val order = cert.order
    implicit val co = CertFormula certFormulaOrdering order

    val watchable =
      (cert.assumedFormulas.iterator filterNot assumedFormulasL0).toArray
    try {
      Sorting stableSort watchable
    } catch {
      case t : Throwable =>
        throw new Exception("ill-formed certificate, incorrect order: " + cert)
    }

    val record = new LemmaRecord(cert, watchable, certNum)
    certNum = certNum + 1

//println("watchable (" + watchable.size + "/" + cert.assumedFormulas.size + ")")
//record.printWatchable

    if (watchCertificate(record) != null)
      pendingCertificates += record
  }

  /**
   * Notify that the given constants have to be invalidated, since they
   * were only used in a certain sub-proof that has now been left.
   */
  def addObsoleteConstants(consts : Iterable[ConstantTerm]) : Unit = {
    val constsSet = consts.toSet
    obsoleteConstants ++= consts

    literals2Certs retain {
      case (a, _) => Seqs.disjoint(a.constants, constsSet)
    }
  }

  /**
   * Add a certificate to the database. The method returns
   * <code>null</code> if some assumed literal of the certificate
   * is not yet known, and can be watched; an updated lemma record
   * otherwise.
   */
  private def watchCertificate(record : LemmaRecord) : LemmaRecord = {
    val notAssumed = record.watchable.iterator filterNot assumedFormulas

    if (notAssumed.hasNext) {
      val key = randomPick(notAssumed)

      if (!(obsoleteConstants.isEmpty ||
            Seqs.disjoint(key.constants, obsoleteConstants))) {
        // if the certificate contains obsolete constants, it can be dropped
        null
      } else if (assumedFormulasL0 contains key) {
        // then additional formulas have been assumed on level 0 after creating
        // the lemma record, an update is necessary
        watchCertificate(updateRecord(record))
      } else {
        literals2Certs.put(key, record :: literals2Certs.getOrElse(key, List()))
//println("assigning new watched literal")
        null
      }

    } else {

      if (obsoleteConstants.isEmpty ||
          Seqs.disjoint(record.cert.constants, obsoleteConstants))
        record
      else
        // if the certificate contains obsolete constants, it can be dropped
        null

    }
  }

  /**
   * Update the watchable literals stored in the given lemma record.
   */
  private def updateRecord(record : LemmaRecord) : LemmaRecord = {
//println("updating certificate #" + record.id)
    val newWatchable = record.watchable filterNot assumedFormulasL0
    new LemmaRecord (record.cert, newWatchable, record.id)
  }

  private val rand = new scala.util.Random(654321)

  private def randomPick[A](it : Iterator[A]) : A = {
    val x = it.next
    if (it.hasNext && rand.nextBoolean)
      randomPick(it)
    else
      x
  }
}
