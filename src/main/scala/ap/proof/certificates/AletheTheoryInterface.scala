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
import ap.terfor.{Formula, TermOrder, Term}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom

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

trait AletheFormulaPrinterContext {

  /**
   * Print a formula in Alethe format to stdout.
   */
  def printFormula(f : CertFormula, variables : List[String]) : Unit

  /**
   * Print a term in Alethe format to stdout.
   */
  def printTerm(t : Term, variables : List[String]) : Unit

}

trait AlethePrinterContext {

  /**
   * Print a comment that is part of an Alethe proof.
   */
  def printlnComment(o : Any) : Unit

  /**
   * Retrieve the label of some formula in the proof.
   */
  def l(f : Conjunction) : String = l(CertFormula(f))

  /**
   * Retrieve the label of some formula in the proof.
   */
  def l(f : CertFormula) : String

  def printAxiomSplit(
                rule            : String,
                assumptions     : Seq[Formula],
                cases           : Seq[Conjunction],
                nextInferences  : List[BranchInference],
                nextAssumptions : List[Set[CertFormula]],
                childCert       : Certificate) : Unit

  /**
   * Printing a sequence of inferences and subsequent certificate in Alethe
   * format.
   */
  def continuePrinting(
                inferences      : List[BranchInference],
                childCert       : Certificate) : Unit

  /**
   * Derive the clause <code>!f1, !f2, ..., !fn</code> specified by the 
   * argument <code>assumptions</code>, reasoning by contradiction using the
   * given certificate. The result is the label of the derived clause.
   */
  def printSubproof(
                subCert         : Certificate,
                assumptions     : Seq[CertFormula]) : String

  /**
   * Introduce a clause by applying a rule and return the label of the clause.
   */
  def introduceClauseThroughStep(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                clause          : Seq[(CertFormula, Boolean)],
                extraAttributes : Seq[(String, String)] = List()) : String

  /**
   * Introduce a clause in which each literal can be a conjunction of formulas
   * by applying a rule and return the label of the clause.
   */
  def introduceMultiClauseThroughStep(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                clause          : Seq[Seq[(CertFormula, Boolean)]],
                extraAttributes : Seq[(String, String)] = List()) : String

  /**
   * Introduce a formula by applying a rule and return the label of the formula.
   */
  def introduceFormulaThroughStep(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                newFormula      : Option[CertFormula],
                extraAttributes : Seq[(String, String)] = List()) : String

  /**
   * Apply the resolution rule with the given <code>nucleus</code> and
   * <code>electrons</code> to derive the formula <code>result</code>, return
   * the label of the new formula.
   */
  def hyperResolution(
                nucleus         : CertFormula,
                electrons       : Seq[CertFormula],
                result          : CertFormula) : String

  /**
   * Apply the resolution rule with the given <code>nucleusLabel</code> and
   * <code>electrons</code> to derive the formula <code>result</code>, return
   * the label of the new formula.
   */
  def hyperResolution(
                nucleusLabel    : String,
                electrons       : Seq[CertFormula],
                result          : CertFormula) : String

  /**
   * Apply the resolution rule with the given <code>nucleusLabel</code> and
   * <code>electronLabels</code> to derive a formula described by the String
   * <code>resultFormula</code>, return the label of the new formula.
   */
  def hyperResolutionStr(
                nucleusLabel    : String,
                electronLabels  : Seq[String],
                resultFormula   : String) : String

}

trait AletheTheoryPrinter {

  /**
   * Print an inference introducing a theory axiom in Alethe syntax to stdout.
   */
  def printTheoryAxiomInference(inference       : TheoryAxiomInference,
                                nextInferences  : List[BranchInference],
                                nextAssumptions : List[Set[CertFormula]],
                                childCert       : Certificate,
                                order           : TermOrder,
                                ctxt            : AlethePrinterContext) : Unit

  /**
   * Ask a theory to print an atom in Alethe syntax to stdout; the predicate of
   * the atom has to part of the theory signature. If the method returns
   * <code>true</code>, the atom has been printed successfully, otherwise
   * the theory is unable to handle the atom.
   */
  def printTheoryAtom(a         : Atom,
                      variables : List[String],
                      ctxt      : AletheFormulaPrinterContext) : Boolean

  /**
   * Check whether an atom (with a predicate belonging to a theory) should be
   * hidden in Alethe proofs.
   */
  def hideTheoryAtom(a : Atom) : Boolean

}

/*
class DistributedAletheTheoryPrinter extends AletheTheoryPrinter {

  def printTheoryAxiomInference(inference       : TheoryAxiomInference,
                                nextInferences  : List[BranchInference],
                                nextAssumptions : List[Set[CertFormula]],
                                childCert       : Certificate,
                                order           : TermOrder,
                                ctxt            : AlethePrinterContext) : Unit={
    inference.theoryRule match {
      case rule : AlethePrintingTheoryRule =>
        rule.printAletheTAI(inference,
                            nextInferences, nextAssumptions,
                            childCert, order, ctxt)
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
                     order           : TermOrder,
                     ctxt            : AlethePrinterContext) : Unit

}
*/
