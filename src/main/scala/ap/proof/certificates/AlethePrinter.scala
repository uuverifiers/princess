/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates;

import ap.DialogUtil
import ap.terfor.preds.Predicate
import ap.parser.{PartName, TPTPLineariser, SMTLineariser, PrincessLineariser,
                  Internal2InputAbsy, IFunction, Transform2NNF,
                  VariableSortInferenceVisitor, TPTPTParser}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, Term}
import ap.basetypes.IdealInt

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}
import scala.util.Sorting

object AlethePrinter {
  private val LINE_WIDTH = 80

  private val NUMERIC_LABEL = """\(([0-9]+)\)""".r

  class AletheFormulaPrinter(predTranslation : Map[Predicate, IFunction])
        extends CertificatePrettyPrinter.FormulaPrinter(predTranslation) {
    def for2String(f : CertFormula) : String =
      ap.DialogUtil.asString {
        f match {
          case CertInequality(lc) => {
            print("(<= 0 ")
            printLC(lc)
            print(")")
          }
          case CertEquation(LinearCombination.Difference(left, right)) => {
            print("(= ")
            printTerm(left)
            print(" ")
            printTerm(right)
            print(")")
          }
          case CertEquation(lc) => {
            print("(= 0 ")
            printLC(lc)
            print(")")
          }
          case CertNegEquation(LinearCombination.Difference(left, right)) => {
            print("(not (= ")
            printTerm(left)
            print(" ")
            printTerm(right)
            print("))")
          }
          case CertNegEquation(lc) => {
            print("(not (= 0 ")
            printLC(lc)
            print("))")
          }
          case CertCompoundFormula(c) => {
            print(for2StringRec(c))
          }
          case f =>
            SMTLineariser applyNoPrettyBitvectors translate(f)
        }
      }

    private def for2StringRec(c : Conjunction) : String =
      if (c.isTrue) {
        "true"
      } else if (c.isFalse) {
        "false"
      } else if (c.isNegatedConjunction) {
        f"(not ${for2StringRec(c.negatedConjs.head)})"
      } else {
        // TODO: predicates
        "(and " +
        ((c.arithConj.positiveEqs.map(CertEquation(_)) ++
          c.arithConj.negativeEqs.map(CertNegEquation(_)) ++
          c.arithConj.inEqs.map(CertInequality(_))).map(for2String _) ++
         c.negatedConjs.map(for2StringRec _).map(x => f"(not $x)"))
         .mkString(" ") + ")"
      }

    private def printTerm(t : Term) : Unit =
      SMTLineariser applyNoPrettyBitvectors translate(t)
    private def printLC(lc : LinearCombination) : Unit =
      SMTLineariser applyNoPrettyBitvectors translate(lc)

    def term2String(t : LinearCombination) : String =
      ap.DialogUtil.asString { printLC(t) }

    def partName2String(pn : PartName) : String =
      pn.toString
  }
}

class AlethePrinter(
        formulaPrinter : CertificatePrettyPrinter.FormulaPrinter) {

  import CertificatePrettyPrinter._
  import AlethePrinter._
  import PartName.{predefNames, predefNamesSet}
  import formulaPrinter.{for2String, term2String, partName2String}

  private def number2String(n : IdealInt) : String =
    term2String(LinearCombination(n))

  def apply(dagCertificate : Seq[Certificate],
            initialFormulas : Map[PartName, CertFormula]) : Unit = {
    certificateNum = dagCertificate.size
    val assumedFormulas = dagCertificate.last.assumedFormulas

    val partNamesSet = initialFormulas.keySet
    val partNames =
      (partNamesSet filterNot predefNamesSet).toIndexedSeq.sortBy(_.toString) ++
      (predefNames filter partNamesSet).toIndexedSeq

    val (usedNames, unusedNames) = partNames partition {
      name => assumedFormulas contains initialFormulas(name)
    }

    println("; Assumptions after simplification:")
    println("; ---------------------------------")

    push
    try {
      for (name <- usedNames) {
        println()
        val label = name match {
          case PartName.NO_NAME         => "input"
          case PartName.FUNCTION_AXIOMS => "function-axioms"
          case PartName.THEORY_AXIOMS   => "theory-axioms"
          case _                        => partName2String(name)
        }
        introduceFormulaThroughAssumption(initialFormulas(name), label)
      }

      if (!(unusedNames forall PartName.predefNamesSet)) {
        println()
        push
        addPrefix("; ")
        println("; Further assumptions not needed in the proof:")
        println("; --------------------------------------------")
        printlnPrefBreaking("",
                            (unusedNames filterNot PartName.predefNamesSet)
                              .map(partName2String _)
                              .mkString(", "))
        pop
      }

      println()
      println("; Those formulas are unsatisfiable:")
      println("; ---------------------------------")

      println()
      println("; Begin of proof")
      printCertificate(dagCertificate.last)
      printlnPref
    } finally {
      reset
    }
    println("; End of proof")

    for (id <- (certificateNum - 2) to 0 by -1) {
      val cert = dagCertificate(id)

      println()
      println("Sub-proof #" + (certificateNum - id - 1) +
              " shows that the following formulas are inconsistent:")
      println("----------------------------------------------------------------")

      push
      try {
        for (f <- cert.assumedFormulas)
          introduceFormula(f)

        println()
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

        if (cnt - lastSplitPos > remLineWidth - 2*lastSplitParenNum - 1 &&
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
                          for2String(f))
      formulaLabel.put(f, "" + formulaCounter)
      formulaCounter = formulaCounter + 1
    } else {
      printlnPref("  (" + label + ")")
      printlnPrefBreaking("  ", for2String(f))
      formulaLabel.put(f, label)
      printPref
    }

  private def printCommand(cmd        : String,
                           label      : String,
                           formulas   : Seq[(CertFormula, Boolean)],
                           attributes : Seq[(String, String)],
                           useCl      : Boolean = true) : Unit = {
    val formulasStr =
      for ((f, neg) <- formulas; fString = for2String(f))
      yield (if (neg) f"(not $fString)" else fString)
    printCommandStr(cmd, label, formulasStr, attributes, useCl)
  }

  private def printCommandStr(cmd        : String,
                              label      : String,
                              formulas   : Seq[String],
                              attributes : Seq[(String, String)],
                              useCl      : Boolean = true) : Unit = {
    val formulasString = formulas.mkString(" ")
    val line =
      f"($cmd $label " +
      (if (useCl) f"(cl $formulasString)" else formulasString) +
      (for ((a, b) <- attributes) yield f" :$a $b").mkString("") +
      ")"
    printlnPrefBreaking("", line)
  }

  private def step(formulas   : Seq[String],
                   attributes : (String, String)*) : String = {
    val l = freshLabel()
    printCommandStr("step", l, formulas, attributes)
    l
  }

  private def closeByEqv(formula : CertFormula,
                         rule    : String) : Unit = {
    val formulaLabel = l(formula)
    val forStr = for2String(formula)
    val eqvForStr = s"(= $forStr false)"
    val l1 = step(List(eqvForStr), ("rule", rule))
    val l2 = step(List(s"(not $eqvForStr)", s"(not $forStr)", "false"),
                  ("rule", "equiv_pos2"))
    val l3 = step(List("(not false)"), ("rule", "false"))
    val l4 = step(List(),
                  ("rule", "resolution"),
                  ("premises", s"($formulaLabel $l1 $l2 $l3)"))
  }

  private def introduceFormulaThroughAssumption(
                        f               : CertFormula,
                        label           : String = "") : Unit = {
    val finalLabel = if (label == "") freshLabel() else label
    printCommand("assume", finalLabel, List((f, false)), List(), useCl = false)
    formulaLabel.put(f, finalLabel)
  }

  private def introduceFormulaThroughStep(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                f               : Option[CertFormula],
                label           : String = "",
                extraAttributes : Seq[(String, String)] = List()) : Unit = {
    val finalLabel = if (label == "") freshLabel() else label

    val attributes =
      List(("rule", ruleName)) ++
      (if (assumedFormulas.isEmpty) List()
       else List(("premises", f"(${l(assumedFormulas)})"))) ++
      extraAttributes

    printCommand("step", finalLabel, f.toSeq.map((_, false)), attributes)
    
    for (g <- f)
      formulaLabel.put(g, finalLabel)
  }

  private def introduceFormulaThroughResolution(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                f               : CertFormula,
                label           : String = "",
                extraAttributes : Seq[(String, String)] = List())
                                : Unit = {
    // we first introduce a tautological clause, and then use resolution
    // to derive what we want

    val interLabel = freshLabel()
    val finalLabel = if (label == "") freshLabel() else label

    printCommand("step", interLabel,
                 List((f, false)) ++ assumedFormulas.map((_, true)),
                 List(("rule", ruleName)) ++ extraAttributes)

    val attributes =
      List(("rule", "resolution")) ++
      (if (assumedFormulas.isEmpty) List()
      else List(("premises", f"(${l(assumedFormulas)} $interLabel)")))
    printCommand("step", finalLabel, List((f, false)), attributes)
    
    formulaLabel.put(f, finalLabel)
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

  private def introduceFormulasThroughStepIfNeeded
                (ruleName            : String,
                 assumedFormulas     : Iterable[CertFormula],
                 fs                  : Iterable[CertFormula],
                 assumedNextFormulas : Set[CertFormula],
                 order               : TermOrder,
                 argComputer         : Option[CertFormula => String] = None)
                                     : Unit = {
    var neededFors = 
      (for (f <- fs.iterator;
            if (!(formulaLabel contains f) && (assumedNextFormulas contains f)))
       yield f).toArray

    // if possible (and necessary), sort the list of formulas
    if (neededFors.size > 1 &&
        (neededFors forall (order isSortingOf _))) {
      implicit val o = CertFormula certFormulaOrdering order
      Sorting stableSort neededFors
    }

    for (f <- neededFors) {
      val args =
        for (comp <- argComputer.toSeq) yield ("arg", comp(f))
      introduceFormulaThroughStep(ruleName, assumedFormulas, Some(f),
                                  extraAttributes = args)
    }
  }

  private def freshLabel() : String = {
    val r = "t" + formulaCounter
    formulaCounter = formulaCounter + 1
    r
  }

  private def l(f : CertFormula) : String = formulaLabel(f)

  private def l(fs : Iterable[CertFormula]) : String =
    ((fs.toSeq map (l(_))).sortBy {
      case NUMERIC_LABEL(num) => ("0" * (9 - num.size)) + num
      case label => label
    }) mkString " "

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

    case cert : CutCertificate => {
      printlnPref
      printlnPref("CUT: with " + for2String(cert.cutFormula) + ":")
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

    case CloseCertificate(fors, _)
           if fors.size == 1 &&
              fors.iterator.next.isInstanceOf[CertInequality] => {
      printlnPref
      closeByEqv(fors.iterator.next, "comp_simplify")
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
        //printRewritingRule("ALPHA", inf)
      case _ : ReducePredInference | _ : ReduceInference =>
        printRewritingRule("REDUCE", inf)
      case _ : SimpInference =>
        //printRewritingRule("SIMP", inf)
      case _ : PredUnifyInference =>
        printRewritingRule("PRED_UNIFY", inf)
      case _ : CombineEquationsInference =>
        printRewritingRule("COMBINE_EQS", inf)
      case _ : CombineInequalitiesInference =>
        //printRewritingRule("COMBINE_INEQS", inf)
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
                    ((for (t <- instanceTerms.reverse)
                     yield term2String(t)) mkString ", ") +
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

    val ruleName =
      inf match {
        case _ : AlphaInference => "and"
        case _ => ""
      }

    inf match {
      case _ : AlphaInference => {
        val CertCompoundFormula(c) = inf.assumedFormulas.head
        val ac = c.arithConj
        def opt(n : Int) = if (n == -1) None else Some(n)

        val argComp =
          (f : CertFormula) => {
            val idx =
              f match {
                case CertEquation(lc) =>
                  opt(ac.positiveEqs.indexOf(lc))
                case CertNegEquation(lc) =>
                  for (n <- opt(ac.negativeEqs.indexOf(lc)))
                  yield n + ac.positiveEqs.size
                case CertInequality(lc) =>
                  for (n <- opt(ac.inEqs.indexOf(lc)))
                  yield n + ac.positiveEqs.size + ac.negativeEqs.size
                // TODO: predicates, negations, compound formulas
              }
            idx match {
              case Some(n) => f"($n)"
              case None => "()"
            }
          }

        introduceFormulasThroughStepIfNeeded("and",
                                             inf.assumedFormulas,
                                             inf.providedFormulas,
                                             nextAssumedFormulas,
                                             childOrder,
                                             argComputer = Some(argComp))
      }
      case CombineInequalitiesInference(leftCoeff, _, rightCoeff, _, _, _) =>
        // TODO: use correct argument order
        introduceFormulaThroughResolution(
          "la_generic",
          inf.assumedFormulas,
          inf.providedFormulas.head,
          extraAttributes =
            List(("args",
                  f"(1 ${number2String(leftCoeff)} ${number2String(rightCoeff)})")))
      case inf : SimpInference =>
        introduceFormulaThroughResolution("la_generic",
                                          inf.assumedFormulas,
                                          inf.providedFormulas.head,
                                          extraAttributes =
                                            List(("args", f"(${inf.factor} 1)")))
      case _ =>
        println(f"Not handled: $inf")
    }
        
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
