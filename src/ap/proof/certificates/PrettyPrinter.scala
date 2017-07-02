/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2017 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.DialogUtil
import ap.terfor.preds.Predicate
import ap.parser.{PartName, TPTPLineariser, SMTLineariser, PrincessLineariser,
                  Internal2InputAbsy, IFunction, Transform2NNF}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TermOrder

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}
import scala.util.Sorting

object CertificatePrettyPrinter {

  abstract class FormulaPrinter {
    def for2String(f : CertFormula) : String
    def term2String(t : LinearCombination) : String
  }

  class PrincessFormulaPrinter(predTranslation : Map[Predicate, IFunction])
        extends FormulaPrinter {
    private val translator = new Internal2InputAbsy(predTranslation)

    def for2String(f : CertFormula) : String = DialogUtil.asString {
      PrincessLineariser printExpression Transform2NNF(translator(f.toFormula))
    }
    def term2String(t : LinearCombination) : String = DialogUtil.asString {
      PrincessLineariser printExpression translator(t)
    }
  }

  class TPTPFormulaPrinter(predTranslation : Map[Predicate, IFunction])
        extends FormulaPrinter {
    private val lin = new TPTPLineariser("")
    private val translator = new Internal2InputAbsy(predTranslation)

    def for2String(f : CertFormula) : String = DialogUtil.asString {
      lin printFormula Transform2NNF(translator(f.toFormula))
    }
    def term2String(t : LinearCombination) : String = DialogUtil.asString {
      lin printTerm translator(t)
    }
  }

  class SMTLIBFormulaPrinter(predTranslation : Map[Predicate, IFunction])
        extends FormulaPrinter {
    private val translator = new Internal2InputAbsy(predTranslation)

    def for2String(f : CertFormula) : String =
      SMTLineariser asString Transform2NNF(translator(f.toFormula))

    def term2String(t : LinearCombination) : String =
      SMTLineariser asString translator(t)
  }

  private val LINE_WIDTH = 80

  private val NUMERIC_LABEL = """\(([0-9]+)\)""".r

}

////////////////////////////////////////////////////////////////////////////////

class CertificatePrettyPrinter(
        formulaPrinter : CertificatePrettyPrinter.FormulaPrinter) {

  import CertificatePrettyPrinter._

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

    push
    try {
      for (name <- usedNames) {
        println
        val label = name match {
          case PartName.NO_NAME => "axioms"
          case _ =>                "" + name
        }
        introduceFormula(initialFormulas(name), label)
      }

      if (unusedNames exists (_ != PartName.NO_NAME)) {
        println
        println("Further assumptions not needed in the proof:")
        println("--------------------------------------------")
        printlnPrefBreaking("",
             (unusedNames filterNot (_ == PartName.NO_NAME)) mkString ", ")
      }

      println
      println("Those formulas are unsatisfiable:")
      println("---------------------------------")

      println
      println("Begin of proof")
      addPrefix("| ")
      printCertificate(dagCertificate.last)
      printlnPref
    } finally {
      reset
    }
    println("End of proof")

    for (id <- (certificateNum - 2) to 0 by -1) {
      val cert = dagCertificate(id)

      println
      println("Sub-proof #" + (certificateNum - id - 1) +
              " shows that the following formulas are inconsistent:")
      println("----------------------------------------------------------------")

      push
      try {
        for (f <- cert.assumedFormulas)
          introduceFormula(f)

        println
        println("Begin of proof")
        addPrefix("| ")
        printCertificate(cert)
        printlnPref
      } finally {
        reset
      }
      println("End of proof")
    }
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

  private def printlnPrefBreaking(label : String, o : Any) : Unit = {
    val remLineWidth = (LINE_WIDTH - prefix.size - label.size) max 50
    val text = "" + o

    printPref(label)

    if (text.size <= remLineWidth) {
      println(text)
    } else {
      var cnt = 0
      var parenNum = 0

      var curSplitPos = 0
      var curSplitParenNum = 0
      var lastSplitPos = 0
      var lastSplitParenNum = 0

      while (cnt < text.size) {
        text(cnt) match {
          case '(' | '{' | '[' => parenNum = parenNum + 1
          case ')' | '}' | ']' => parenNum = parenNum - 1
          case ' ' => {
            // this is where we might split
            curSplitPos = cnt
            curSplitParenNum = parenNum
          }
          case _ => // nothing
        }

        if (cnt - lastSplitPos > remLineWidth - 2*lastSplitParenNum &&
            curSplitPos > lastSplitPos) {
          println(text.substring(lastSplitPos, curSplitPos))

          lastSplitPos = curSplitPos + 1
          lastSplitParenNum = curSplitParenNum

          if (lastSplitPos < text.size)
            printPref(" " * label.size + "  " * curSplitParenNum)
        }

        cnt = cnt + 1
      }

      if (lastSplitPos < cnt)
        println(text.substring(lastSplitPos, cnt))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private val formulaLabel = new LinkedHashMap[CertFormula, String]
  private var formulaCounter : Int = 1

  private def introduceFormula(f : CertFormula, label : String = "") : Unit =
    if (label == "") {
      printlnPrefBreaking("  (" + formulaCounter + ")  ",
                          formulaPrinter for2String f)
      formulaLabel.put(f, "" + formulaCounter)
      formulaCounter = formulaCounter + 1
    } else {
      printlnPref("  (" + label + ")")
      printlnPrefBreaking("  ", formulaPrinter for2String f)
      formulaLabel.put(f, label)
      printPref
    }

  private def introduceFormulaIfNeeded
                (f : CertFormula, assumedFormulas : Set[CertFormula]) : Unit = {
    if (!(formulaLabel contains f) && (assumedFormulas contains f))
      introduceFormula(f)
  }

  private def introduceFormulasIfNeeded
                (fs : Iterable[CertFormula],
                 assumedFormulas : Set[CertFormula],
                 order : TermOrder) : Unit = {
    var neededFors = 
      (for (f <- fs.iterator;
            if (!(formulaLabel contains f) && (assumedFormulas contains f)))
       yield f).toArray

    // if possible (and necessary), sort the list of formulas
    if (neededFors.size > 1 &&
        (neededFors forall (order isSortingOf _))) {
      implicit val o = CertFormula certFormulaOrdering order
      Sorting stableSort neededFors
    }

    for (f <- neededFors) introduceFormula(f)
  }

  private def l(f : CertFormula) : String = "(" + formulaLabel(f) + ")"

  private def l(fs : Iterable[CertFormula]) : String =
    ((fs.toSeq map (l(_))).sortBy {
      case NUMERIC_LABEL(num) => "(" + ("0" * (9 - num.size)) + num + ")"
      case label => label
    }) mkString ", "

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

  private def reset : Unit = {
    branchStack.clear
    formulaLabel.clear
    prefix = ""
    formulaCounter = 1
  }

  //////////////////////////////////////////////////////////////////////////////

  private def printCertificate(cert : Certificate) : Unit = cert match {

    case BranchInferenceCertificate(inferences, child, _) => {
      val assumptions =
        computeAssumptions(inferences.toList.tail, child.assumedFormulas)

      for ((inf, assumptions) <- inferences.iterator zip assumptions.iterator)
        printInference(inf, assumptions, child.order)

      printCertificate(child)
    }

    case cert : BetaCertificate => {
      printlnPref
      printlnPref("BETA: splitting " +
                  l(cert.localAssumedFormulas) + " gives:")
      printCases(cert)
    }

    case cert : SplitEqCertificate => {
      printlnPref
      printlnPref("SPLIT-EQ: splitting " +
                  l(cert.localAssumedFormulas) + " gives:")
      printCases(cert)
    }

    case StrengthenCertificate(ineq, _, _, _) => {
      printlnPref
      printlnPrefBreaking("STRENGTHEN: ",
                    "tightening of inequality " + l(ineq) + " gives:")
      printCases(cert)
    }

    case cert : OmegaCertificate => {
      printlnPref
      printlnPref("OMEGA: resolving " +
                  l(cert.localAssumedFormulas) + " by considering:")
      printCases(cert)
    }

    case cert : CloseCertificate => {
      printlnPref
      printlnPrefBreaking("CLOSE: ",
                  l(cert.localAssumedFormulas) + " " +
                  (if (cert.localAssumedFormulas.size == 1) "is" else "are") +
                  " inconsistent.")
    }

    case DagCertificateConverter.ReferenceCertificate(id, localAssumed,
                                                      _, _, _) => {
      printlnPref
      printlnPrefBreaking("REF_CLOSE: ",
                          l(localAssumed) + " " +
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
        printlnPref
        introduceFormulasIfNeeded(cert localProvidedFormulas num,
                                  subCert.assumedFormulas,
                                  subCert.order)
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
                             nextAssumedFormulas : Set[CertFormula],
                             childOrder : TermOrder) : Unit = {
    if (inf == ReusedProofMarker ||
        (inf.localBoundConstants.isEmpty &&
         (inf.providedFormulas forall {
           f => (formulaLabel contains f) || !(nextAssumedFormulas contains f)
         })))
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
      case _ : DirectStrengthenInference =>
        printRewritingRule("STRENGTHEN", inf)
      case _ : AntiSymmetryInference =>
        printRewritingRule("ANTI_SYMM", inf)
      case _ : DivRightInference =>
        printRewritingRule("DIV_RIGHT", inf)
      case inf : TheoryAxiomInference =>
        printRewritingRule("THEORY_AXIOM " + inf.theory, inf)
      case QuantifierInference(quantifiedFormula, newConstants, _, _) =>
        printlnPrefBreaking("DELTA: ",
                    "instantiating " +  l(quantifiedFormula) +
                    " with fresh " +
                    (if (newConstants.size > 1) "symbols" else "symbol") + " " +
                    (newConstants mkString ", ") + " gives:")
      case GroundInstInference(quantifiedFormula, instanceTerms,
                               _, dischargedAtoms, _, _) =>
        printlnPrefBreaking("GROUND_INST: ",
                    "instantiating " +  l(quantifiedFormula) + " with " +
                    ((for (t <- instanceTerms)
                    yield (formulaPrinter term2String t)) mkString ", ") +
                    (if (!dischargedAtoms.isEmpty)
                       ", simplifying with " + l(dischargedAtoms)
                     else
                       "") +
                    " gives:")
      case ColumnReduceInference(_, newSymbol, definingEq, _, _) =>
        printlnPrefBreaking("COL_REDUCE: ",
                    "introducing fresh symbol " + newSymbol +
                    " defined by:")
    }

    introduceFormulasIfNeeded(inf.providedFormulas,
                              nextAssumedFormulas,
                              childOrder)
  }

  private def printRewritingRule(name : String, inf : BranchInference) : Unit =
    printlnPrefBreaking(name + ": ",
                        l(inf.assumedFormulas) +
                        (inf.assumedFormulas.size match {
                          case 0 => ""
                          case 1 => " implies:"
                          case _ => " imply:"
                         }))

}