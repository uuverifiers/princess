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

import ap.parser.PartName
import ap.terfor.linearcombination.LinearCombination

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}

object CertificatePrettyPrinter {

  abstract class FormulaPrinter {
    def printFor(f : CertFormula) : Unit
    def term2String(t : LinearCombination) : String
  }

  class TPTPFormulaPrinter extends FormulaPrinter {
    def printFor(f : CertFormula) : Unit = println(f)
    def term2String(t : LinearCombination) : String = t.toString
  }

}

class CertificatePrettyPrinter(
        formulaPrinter : CertificatePrettyPrinter.FormulaPrinter) {

  def apply(dagCertificate : Seq[Certificate],
            initialFormulas : Map[PartName, CertFormula]) : Unit = {
    certificateNum = dagCertificate.size
    val assumedFormulas = dagCertificate.last.assumedFormulas

    val partNames =
      (initialFormulas.iterator map (_._1)).toIndexedSeq.sortWith {
        case (PartName.NO_NAME, _) => false
        case (_, PartName.NO_NAME) => true
        case (a, b) => a.toString < b.toString
      }

    val (usedNames, unusedNames) = partNames partition {
      name => assumedFormulas contains initialFormulas(name)
    }

    println("Assumptions after simplification:")
    println("---------------------------------")

    for (name <- usedNames) {
      println
      val label = name match {
        case PartName.NO_NAME =>
          "axioms"
        case _ =>
          "" + name
      }
      introduceFormula(initialFormulas(name), label)
    }

    if (unusedNames exists (_ != PartName.NO_NAME)) {
      println
      println("Further assumptions not needed in the proof:")
      println("--------------------------------------------")
      println((unusedNames filterNot (_ == PartName.NO_NAME)) mkString ", ")
    }

    println
    println("Those formulas are unsatisfiable:")
    println("---------------------------------")

    printCertificate(dagCertificate.last)

/*
    for (id <- (certificateNum - 2) to 0 by -1) {
      println
      println("Sub-proof #" + (certificateNum - id - 1) + ":")
      println("-------------")
      printCertificate(dagCertificate(id))
    }
*/
  }

  private var certificateNum = 0

  //////////////////////////////////////////////////////////////////////////////

  private var prefix = ""

  private def addPrefix(s : String) : Unit =
    prefix = prefix + s

  private def printlnPref : Unit =
    println(prefix)

  private def printPref : Unit =
    print(prefix)

  private def printlnPref(o : Any) : Unit = {
    print(prefix)
    println(o)
  }

  private def printPref(o : Any) : Unit = {
    print(prefix)
    print(o)
  }

  //////////////////////////////////////////////////////////////////////////////

  private val formulaLabel = new LinkedHashMap[CertFormula, String]
  private var formulaCounter : Int = 1

  private def introduceFormula(f : CertFormula, label : String = "") : Unit = {
    if (label == "") {
      printPref("  (" + formulaCounter + ")  ")
      formulaLabel.put(f, "" + formulaCounter)
      formulaCounter = formulaCounter + 1
    } else {
      printlnPref("  (" + label + ")")
      formulaLabel.put(f, label)
      printPref
    }

    print("  ")
    formulaPrinter printFor f
  }

  private def introduceFormulaIfNeeded
                (f : CertFormula, assumedFormulas : Set[CertFormula]) : Unit = {
    if (!(formulaLabel contains f) && (assumedFormulas contains f))
      introduceFormula(f)
  }

  private def l(f : CertFormula) : String = "(" + formulaLabel(f) + ")"

  private def l(fs : Seq[CertFormula]) : String = (fs map (l(_))) mkString ", "

  //////////////////////////////////////////////////////////////////////////////

  private val branchStack = new ArrayStack[(Int, String)]

  private def push : Unit =
    branchStack push ((formulaLabel.size, prefix))

  private def pop : Unit = {
    val (oldFormulaLabelSize, oldPrefix) = branchStack.pop
    while (formulaLabel.size > oldFormulaLabelSize)
      formulaLabel -= formulaLabel.last._1
    prefix = oldPrefix
  }

  //////////////////////////////////////////////////////////////////////////////

  private def printCertificate(cert : Certificate) : Unit = cert match {

    case BranchInferenceCertificate(inferences, child, _) => {
      val assumptions =
        computeAssumptions(inferences.toList.tail, child.assumedFormulas)

      for ((inf, assumptions) <- inferences.iterator zip assumptions.iterator)
        printInference(inf, assumptions)

      printCertificate(child)
    }

    case cert : BetaCertificate => {
      printlnPref
      printlnPref("BETA: splitting " +
                  l(cert.localAssumedFormulas.toSeq) + " gives:")
      printCases(cert)
    }

    case cert : CloseCertificate => {
      printlnPref
      printlnPref("CLOSE: " + l(cert.localAssumedFormulas.toSeq) + " " +
                  (if (cert.localAssumedFormulas.size == 1) "is" else "are") +
                  " inconsistent.")
    }

    case DagCertificateConverter.ReferenceCertificate(id, localAssumed,
                                                      _, _, _) => {
      printlnPref
      printlnPref("REF_CLOSE: " + l(localAssumed.toSeq) + " " +
                  (if (localAssumed.size == 1) "is" else "are") +
                  " inconsistent by sub-proof #" +
                  (certificateNum - id - 1) + ".")
    }
  }

  private def printCases(cert : Certificate) : Unit = {
    var num = 0
    printlnPref
    for (subCert <- cert.subCertificates) {
      push
      try {
        printlnPref("Case " + (num + 1) + ":")
        addPrefix("| ")
        for (f <- cert localProvidedFormulas num)
          introduceFormulaIfNeeded(f, subCert.assumedFormulas)
        printCertificate(subCert)
        printlnPref
      } finally {
        pop
      }
      num = num + 1
    }
    printlnPref("End of split")
  }

  private def computeAssumptions(infs : List[BranchInference],
                                 childAssumptions : Set[CertFormula])
                                : List[Set[CertFormula]] = infs match {
    case List() => List(childAssumptions)
    case inf :: remInfs => {
      val subRes@(lastA :: _) =
        computeAssumptions(remInfs, childAssumptions)
      (lastA -- inf.providedFormulas ++ inf.assumedFormulas) :: subRes
    }
  }

  private def printInference(inf : BranchInference,
                             nextAssumedFormulas : Set[CertFormula]) : Unit = {
    if (inf == ReusedProofMarker)
      return

    printlnPref

    inf match {
      case _ : AlphaInference =>
        printRewritingRule("ALPHA", inf)
      case _ : ReducePredInference | _ : ReduceInference =>
        printRewritingRule("REDUCE", inf)
      case _ : SimpInference =>
        printRewritingRule("SIMP", inf)
      case _ : PredUnifyInference =>
        printRewritingRule("PRED_UNIFY", inf)
      case _ : CombineEquationsInference =>
        printRewritingRule("COMBINE_EQS", inf)
      case _ : CombineInequalitiesInference =>
        printRewritingRule("COMBINE_INEQS", inf)
      case QuantifierInference(quantifiedFormula, newConstants, _, _) =>
        printlnPref("DELTA: instantiating " +  l(quantifiedFormula) +
                    " with fresh " +
                    (if (newConstants.size > 1) "symbols" else "symbol") + " " +
                    (newConstants mkString ", ") + " gives:")
      case GroundInstInference(quantifiedFormula, instanceTerms,
                               _, dischargedAtoms, _, _) => {
        printPref("GROUND_INST: instantiating " +  l(quantifiedFormula) +
                  " with " +
                  ((for (t <- instanceTerms) yield (formulaPrinter term2String t))
                  mkString ", "))
        if (!dischargedAtoms.isEmpty) {
          println(",")
          printPref("             simplifying with " + l(dischargedAtoms))
        }
        println(" gives:")
      }
    }

    for (f <- inf.providedFormulas)
      introduceFormulaIfNeeded(f, nextAssumedFormulas)
  }

  private def printRewritingRule(name : String, inf : BranchInference) : Unit =
    printlnPref(name + ": " + l(inf.assumedFormulas.toSeq) + " " +
                (inf.assumedFormulas.size match {
                  case 0 => "have:"
                  case 1 => "implies:"
                  case _ => "imply:"
                 }))

}