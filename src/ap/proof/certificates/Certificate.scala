/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.certificates

import ap.terfor.{TermOrder, SortedWithOrder}
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, FilterIt, LRUCache, Seqs}

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
abstract class Certificate extends Seq[Certificate] {

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(Certificate.AC,
                   (closingConstraint isSortedBy order) &&
                   size == localProvidedFormulas.size &&
                   (assumedFormulas forall (_ isSortedBy order)))
  //////////////////////////////////////////////////////////////////////////////

  /**
   * The constraint resulting from this proof
   */
  val closingConstraint : Conjunction
  
  /**
   * Formulae that the proof assumes to be present on this branch (i.e.,
   * premisses of rules applied in the proof). We assume that all formulae
   * live in the antecedent.
   */
  lazy val assumedFormulas : Set[Conjunction] =
    localAssumedFormulas ++
    (for ((cert, providedFormulas) <- elements zip localProvidedFormulas.elements;
          f <- FilterIt(cert.assumedFormulas.elements,
                        (f : Conjunction) => !(providedFormulas contains f))) yield f)
  
  val localAssumedFormulas : Set[Conjunction]
  
  /**
   * Formulae that are introduced into the antecedent by this rule application
   * (one set for each subproof). This will implicitly simplify formulae (all
   * simplifications that are built into the datastructures are carried out).
   */
  val localProvidedFormulas : Seq[Set[Conjunction]]

  val order : TermOrder

  def inferenceCount : Int = (1 /: this) { case (num, cert) => num + cert.inferenceCount }
  
}

////////////////////////////////////////////////////////////////////////////////

object PartialCertificate {
  
  private val AC = Debug.AC_CERTIFICATES
  
  val IDENTITY = new PartialCertificate((x : Seq[Certificate]) => x.first, 1)
  
  private val failingCertificateCache =
    new LRUCache[Int, PartialCertificate] (100)
  
  def FAIL(arity : Int) = failingCertificateCache(arity) {
    new PartialCertificate((_ : Seq[Certificate]) =>
                             throw new UnsupportedOperationException,
                           arity)
  } 
  
  def apply(f : Seq[Certificate] => Certificate, arity : Int) =
    new PartialCertificate(f, arity)
  
}

/**
 * Class to store fragments of certificates. Such fragments can be seen as
 * functions from sequences of certificates (the certificates derived from
 * some subproofs) to certificates. In this sense, every rule application
 * is justified by a partial certificate.
 */
class PartialCertificate private (f : Seq[Certificate] => Certificate, val arity : Int)
      extends (Seq[Certificate] => Certificate) {

  def apply(subCerts : Seq[Certificate]) : Certificate = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == subCerts.size)
    ////////////////////////////////////////////////////////////////////////////
    f(subCerts)
  }

  def compose(that : Seq[PartialCertificate]) : PartialCertificate = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(PartialCertificate.AC, arity == that.size)
    ////////////////////////////////////////////////////////////////////////////
    
    val newArity = (0 /: (that.elements map (_.arity)))(_ + _)
    
    val newF = (certs : Seq[Certificate]) => {
      val subRes = new ArrayBuffer[Certificate]
      var offset : Int = 0
      for (pc <- that) {
        subRes += pc(certs.slice(offset, offset + pc.arity))
        offset = offset + arity
      }
      apply(subRes)
    }
    
    new PartialCertificate(newF, newArity)
  }
}