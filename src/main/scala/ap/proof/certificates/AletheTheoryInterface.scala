/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.theories.Theory
import ap.terfor.Formula
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object AletheTheoryRegistry {

  private val theoryPrinters = new MHashMap[Theory, AletheTheoryPrinter]

  def register(theory : Theory, printer : AletheTheoryPrinter) : Unit =
    synchronized {
      theoryPrinters.put(theory, printer)
    }

  def lookup(theory : Theory) : Option[AletheTheoryPrinter] =
    synchronized {
      theoryPrinters.get(theory)
    }

}

trait AlethePrinterContext {

  /**
   * Retrieve the label of some formula in the proof.
   */
  def l(f : Conjunction) : String = l(CertFormula(f))

  /**
   * Retrieve the label of some formula in the proof.
   */
  def l(f : CertFormula) : String

  def printAxiomSplit(assumptions     : Seq[Formula],
                      cases           : Seq[Conjunction],
                      nextInferences  : List[BranchInference],
                      nextAssumptions : List[Set[CertFormula]],
                      childCert       : Certificate) : Unit

  def continuePrinting(inferences  : List[BranchInference],
                       assumptions : List[Set[CertFormula]],
                       childCert   : Certificate) : Unit

}

trait AletheTheoryPrinter {

  def printTheoryAxiomInference(inference       : TheoryAxiomInference,
                                nextInferences  : List[BranchInference],
                                nextAssumptions : List[Set[CertFormula]],
                                childCert       : Certificate,
                                ctxt            : AlethePrinterContext) : Unit

}

class DistributedAletheTheoryPrinter extends AletheTheoryPrinter {

  def printTheoryAxiomInference(inference       : TheoryAxiomInference,
                                nextInferences  : List[BranchInference],
                                nextAssumptions : List[Set[CertFormula]],
                                childCert       : Certificate,
                                ctxt            : AlethePrinterContext) : Unit={
    inference.theoryRule match {
      case rule : AlethePrintingTheoryRule =>
        rule.printAletheTAI(inference,
                            nextInferences, nextAssumptions,
                            childCert, ctxt)
      case rule =>
        throw new Exception("do not know how to print theory rule " + rule)
    }
  }

}

trait AlethePrintingTheoryRule extends TheoryRule {

  def printAletheTAI(inference       : TheoryAxiomInference,
                     nextInferences  : List[BranchInference],
                     nextAssumptions : List[Set[CertFormula]],
                     childCert       : Certificate,
                     ctxt            : AlethePrinterContext) : Unit

}