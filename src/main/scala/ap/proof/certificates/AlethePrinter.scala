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
import ap.terfor.preds.{Atom, Predicate}
import ap.parser.{PartName, TPTPLineariser, SMTLineariser, PrincessLineariser,
                  Internal2InputAbsy, IFunction, Transform2NNF,
                  VariableSortInferenceVisitor, TPTPTParser}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.{TermOrder, Term, OneTerm, VariableTerm, ConstantTerm}
import ap.basetypes.IdealInt

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                 ArrayStack}
import scala.util.Sorting
import java.security.cert.CertificateFactory

object AlethePrinter {
  private val LINE_WIDTH = 80

  private val NUMERIC_LABEL = """\(([0-9]+)\)""".r

  class AletheFormulaPrinter(predTranslation : Map[Predicate, IFunction])
        extends CertificatePrettyPrinter.FormulaPrinter(predTranslation) {

    def for2String(f : CertFormula) : String =
      ap.DialogUtil.asString { printFor(f, List()) }

    def printFor(f         : CertFormula,
                 variables : List[String]) : Unit =
        f match {
          case CertInequality(lc) => {
            print("(<= 0 ")
            printLC(lc, variables)
            print(")")
          }
          case CertEquation(LinearCombination.Difference(left, right)) => {
            print("(= ")
            printTerm(left, variables)
            print(" ")
            printTerm(right, variables)
            print(")")
          }
          case CertEquation(lc) => {
            print("(= 0 ")
            printLC(lc, variables)
            print(")")
          }
          case CertNegEquation(LinearCombination.Difference(left, right)) => {
            print("(not (= ")
            printTerm(left, variables)
            print(" ")
            printTerm(right, variables)
            print("))")
          }
          case CertNegEquation(lc) => {
            print("(not (= 0 ")
            printLC(lc, variables)
            print("))")
          }
          case CertPredLiteral(false, atom) => {
            printAtom(atom, variables)
          }
          case CertPredLiteral(true, atom) => {
            print("(not ")
            printAtom(atom, variables)
            print(")")
          }
          case CertCompoundFormula(c) => {
            printForRec(c, variables, false)
          }
        }

    private def printTerm(t : Term, variables : List[String]) : Unit =
      t match {
        case OneTerm =>
          print("1")
        case VariableTerm(ind) =>
          print(variables(ind))
        case c : ConstantTerm =>
          print(SMTLineariser.quoteIdentifier(c.name))
        case lc : LinearCombination =>
          printLC(lc, variables)
      }

    private def printLC(lc : LinearCombination,
                        variables : List[String]) : Unit =
      lc.size match {
        case 0 =>
          print("0")
        case 1 =>
          printOneLC(lc.leadingCoeff, lc.leadingTerm, variables)
        case _ => {
          print("(+")
          for ((coeff, t) <- lc.iterator) {
            print(" ")
            printOneLC(coeff, t, variables)
          }
          print(")")
        }
      }

    private def printOneLC(coeff : IdealInt, t : Term,
                           variables : List[String]) : Unit =
      if (coeff.isOne) {
        printTerm(t, variables)
      } else if (t == OneTerm) {
        print(SMTLineariser.toSMTExpr(coeff))
      } else {
        print("(* ")
        print(SMTLineariser.toSMTExpr(coeff))
        print(" ")
        printTerm(t, variables)
        print(")")
      }

    private def printAtom(a : Atom, variables : List[String]) : Unit =
      if (a.size == 0) {
        print(SMTLineariser.quoteIdentifier(a.pred.name))
      } else {
        print(f"(${SMTLineariser.quoteIdentifier(a.pred.name)}")
        for (t <- a) {
          print(" ")
          printLC(t, variables)
        }
        print(")")
      }

    private def printForRec(c         : Conjunction,
                            variables : List[String],
                            negated   : Boolean) : Unit =
      if (if (negated) c.isFalse else c.isTrue) {
        print("true")
      } else if (if (negated) c.isTrue else c.isFalse) {
        print("false")
      } else if (c.isNegatedConjunction) {
        printForRec(c.negatedConjs.head, variables, !negated)
      } else {
        val N = variables.size
        val needsAnd = c.size > 1

        // TODO: group blocks of quantifiers
        var newVars = variables
        for ((q, n) <- c.quans.reverse.zipWithIndex) {
          val varName = "$v" + (n + N)
          newVars = varName :: newVars
          if ((q == Quantifier.ALL) != negated)
            print("(forall ((")
          else
            print("(exists ((")
          print(f"$varName Int")  // TODO
          print(")) ")
        }

        if (needsAnd) {
          if (negated)
            print("(or")
          else
            print("(and")
        }

        for (lc <- c.arithConj.positiveEqs) {
          print(" ")
          printFor(if (negated) CertNegEquation(lc) else CertEquation(lc),
                   newVars)
        }
        for (lc <- c.arithConj.negativeEqs) {
          print(" ")
          printFor(if (negated) CertEquation(lc) else CertNegEquation(lc),
                   newVars)
        }

        for (lc <- c.arithConj.inEqs) {
          print(" ")
          printFor(if (negated) !CertInequality(lc) else CertInequality(lc),
                   newVars)
        }

        for (a <- c.predConj.positiveLits) {
          print(" ")
          printFor(CertPredLiteral(negated, a), newVars)
        }
        for (a <- c.predConj.negativeLits) {
          print(" ")
          printFor(CertPredLiteral(!negated, a), newVars)
        }

        for (d <- c.negatedConjs) {
          print(" ")
          printForRec(d, newVars, !negated)
        }
        if (needsAnd)
          print(")")

        print(")" * c.quans.size)
      }

    def term2String(t : LinearCombination) : String =
      ap.DialogUtil.asString { printLC(t, List()) }

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

  /**
   * Apply standard rules to a new formula. Among others, every disjunction
   * will be turned into a clause, and <code>false</code> is rewritten to an
   * empty clause. The method will return the new formula label.
   */
  private def postprocessFormula(formula : CertFormula,
                                 label : String) : String = {
    val label2 =
      formula match {
        case CertCompoundFormula(f) if f.isNegatedConjunction =>
          disjunctionToClause(formula, label)
        case f if f.isFalse => {
          val l1 = step(List("(not false)"), ("rule", "false"))
          step(List(), ("rule", "resolution"), ("premises", s"($label $l1)"))
        }
        case _ =>
          label
      }
    formulaLabel.put(formula, label2)
    label2
  }

  private def printCommand(cmd  : String,
                           args : Seq[String]) : Unit = {
    val line = f"(${(cmd +: args).mkString(" ")})"
    printlnPrefBreaking("", line)
  }

  private def printCommand(cmd        : String,
                           label      : String,
                           formulas   : Seq[(CertFormula, Boolean)],
                           attributes : Seq[(String, String)],
                           useCl      : Boolean = true,
                           useOr      : Boolean = false) : Unit = {
    val formulasStr =
      for ((f, neg) <- formulas; fString = for2String(f))
      yield (if (neg) f"(not $fString)" else fString)
    printCommandStr(cmd, label, formulasStr, attributes, useCl, useOr)
  }

  private def printCommandStr(cmd        : String,
                              label      : String,
                              formulas   : Seq[String],
                              attributes : Seq[(String, String)],
                              useCl      : Boolean = true,
                              useOr      : Boolean = false) : Unit = {
    val formulasString =
      formulas.mkString(" ")
    val formulasString2 =
      if (useOr) f"(or $formulasString)" else formulasString
    val formulasString3 =
      if (useCl) f"(cl $formulasString2)" else formulasString2
    printCommand(cmd,
                 List(label, formulasString3) ++
                 (for ((a, b) <- attributes; x <- List(f":$a", b)) yield x))
  }

  private def step(formulas   : Seq[String],
                   attributes : (String, String)*) : String = {
    val l = freshLabel()
    printCommandStr("step", l, formulas, attributes)
    l
  }

  private def stepCertFor(formulas   : Seq[CertFormula],
                          attributes : (String, String)*) : String = {
    val l = freshLabel()
    printCommandStr("step", l, formulas.map(for2String(_)), attributes)
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

  private def asClause(formula : CertFormula) : Seq[CertFormula] =
    formula match {
      case formula if formula.isFalse =>
        List()
      case CertCompoundFormula(f) if f.isNegatedConjunction =>
        f.negatedConjs.head.iterator.map(g => CertFormula(!g)).toVector
      case formula =>
        List(formula)
    }

  private def disjunctionToClause(disjunction : CertFormula,
                                  label       : String) : String =
    disjunction match {
      case CertCompoundFormula(f) if f.isNegatedConjunction => {
        stepCertFor(asClause(disjunction),
                    ("rule", "or"),
                    ("premises", f"($label)"))
      }
      case f =>
        label
    }

  private def hyperResolution(nucleus   : CertFormula,
                              electrons : Seq[CertFormula],
                              result    : CertFormula) : String = {
    val l1 =
      stepCertFor(asClause(result),
                  ("rule", "resolution"),
                  ("premises", f"(${l(electrons)} ${l(nucleus)})"))
    formulaLabel.put(result, l1)
    l1
  }

  private def introduceFormulaThroughAssumption(
                        f               : CertFormula,
                        label           : String = "") : Unit = {
    val finalLabel = if (label == "") freshLabel() else label
    printCommand("assume", finalLabel, List((f, false)), List(), useCl = false)
    postprocessFormula(f, finalLabel)
  }

  private def introduceFormulaThroughStep(
                ruleName        : String,
                assumedFormulas : Iterable[CertFormula],
                newFormula      : Option[CertFormula],
                extraAttributes : Seq[(String, String)] = List()) : Unit = {
    val l1 = freshLabel()

    val attributes =
      List(("rule", ruleName)) ++
      (if (assumedFormulas.isEmpty) List()
       else List(("premises", f"(${l(assumedFormulas)})"))) ++
      extraAttributes

    printCommand("step", l1, newFormula.toSeq.map((_, false)), attributes)
    
    for (g <- newFormula)
      postprocessFormula(g, l1)
  }

  private def introduceFormulaThroughResolution(
                ruleName          : String,
                assumedFormulas   : Iterable[CertFormula],
                introducedFormula : CertFormula,
                label             : String = "",
                extraAttributes   : Seq[(String, String)] = List(),
                swapOrder         : Boolean = false,
                useOr             : Boolean = false)
                                  : String = {
    // we first introduce a tautological clause, and then use resolution
    // to derive what we want

    val interLabel = freshLabel()
    val formulaSeq =
      if (swapOrder)
        assumedFormulas.toSeq.map((_, true)) ++ List((introducedFormula, false))
      else
        List((introducedFormula, false)) ++ assumedFormulas.toSeq.map((_, true))

    printCommand("step", interLabel,
                 formulaSeq,
                 List(("rule", ruleName)) ++ extraAttributes,
                 useOr = useOr)

    val interLabel2 =
      if (useOr) {
        val l = freshLabel()
        printCommand("step", l,
                     formulaSeq,
                     List(("rule", "or"),
                          ("premises", f"($interLabel)")))
        l
      } else {
        interLabel
      }

    val finalLabel = if (label == "") freshLabel() else label

    val attributes =
      List(("rule", "resolution")) ++
      List(("premises", f"(${l(assumedFormulas)} $interLabel2)"))
    printCommand("step", finalLabel,
                 List((introducedFormula, false)), attributes)
    
    formulaLabel.put(introducedFormula, finalLabel)
    finalLabel
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
        for (comp <- argComputer.toSeq) yield ("args", comp(f))
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
      printlnPref("; BETA: splitting " +
                  l(cert.localAssumedFormulas) + " gives:")

      val l1 = printSubproof(cert.subCertificates(0), List(cert.leftFormula))

      // TODO: add the formula to the formulaLabel map, at least in some cases

      printlnPref

      printlnPref("; splitting " +
                  l(cert.localAssumedFormulas) + ", second case:")
      val l2 =
        stepCertFor(asClause(cert.rightFormula),
                    ("rule", "resolution"),
                    ("premises", f"(${l(cert.localAssumedFormulas)} $l1)"))
      formulaLabel.put(cert.rightFormula, l2)

      printCertificate(cert.subCertificates(1))
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

    case CloseCertificate(fors, _)
           if fors.size == 1 &&
              fors.iterator.next.isInstanceOf[CertEquation] => {
      printlnPref
      closeByEqv(fors.iterator.next, "eq_simplify")
    }

    case CloseCertificate(fors, _)
           if fors.size == 1 && fors.iterator.next.isFalse => {
      // in this case, we assume that we have already derived an
      // empty clause, there is nothing left to do
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

  private def printCases(
         cert        : Certificate,
         assumptions : Option[Seq[Seq[CertFormula]]] = None) : Seq[String] = {
    val subproofLabels =
    for ((subCert, num) <- cert.subCertificates.zipWithIndex) yield {
      implicit val o = CertFormula certFormulaOrdering subCert.order
      val branchAssumptions =
        assumptions match {
          case Some(a) => a(num)
          case None    => cert.localProvidedFormulas(num).toSeq.sorted
        }

      printSubproof(subCert, branchAssumptions)
    }

    subproofLabels
  }

  private def printSubproof(subCert     : Certificate,
                            assumptions : Seq[CertFormula]) : String = {
    val endLabel = freshLabel()
    push

    implicit val o = CertFormula certFormulaOrdering subCert.order

    try {
      printCommand("anchor", List(":step", endLabel))
      addPrefix("  ")
      printlnPref

      for (f <- assumptions)
        introduceFormulaThroughAssumption(f)

      printCertificate(subCert)

      printlnPref
    } finally {
      pop
    }

    printCommand("step", endLabel,
                 assumptions.map((_, true)),
                 List(("rule", "subproof")))
    endLabel
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
        //printRewritingRule("COMBINE_EQS", inf)
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
/*        printlnPrefBreaking("GROUND_INST: ",
                    "instantiating " +  l(quantifiedFormula) + " with " +
                    ((for (t <- instanceTerms.reverse)
                     yield term2String(t)) mkString ", ") +
                    (if (!dischargedAtoms.isEmpty)
                       ", simplifying with " + l(dischargedAtoms)
                     else
                       "") +
                    " gives:") */
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
        val pc = c.predConj
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
                case CertPredLiteral(false, a) =>
                  for (n <- opt(pc.positiveLits.indexOf(a)))
                  yield n + ac.size
                case CertPredLiteral(true, a) =>
                  for (n <- opt(pc.negativeLits.indexOf(a)))
                  yield n + ac.size + pc.positiveLits.size
                case CertCompoundFormula(d) =>
                  for (n <- opt(c.negatedConjs.indexOf(!d)))
                  yield n + ac.size + pc.size
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

      case CombineEquationsInference(equations, _, _) => {
        val (coeffs, eqs) = equations.unzip
        introduceFormulaThroughResolution(
          "la_generic",
          eqs,
          inf.providedFormulas.head,
          extraAttributes =
            List(("args",
                  f"((- 1) ${coeffs.map(number2String(_)).mkString(" ")})")))
      }

      case inf : SimpInference =>
        introduceFormulaThroughResolution("la_generic",
                                          inf.assumedFormulas,
                                          inf.providedFormulas.head,
                                          extraAttributes =
                                            List(("args", f"(${inf.factor} 1)")))

      case GroundInstInference(quantifiedFormula, instanceTerms,
                               _, dischargedAtoms, result, order) => {
        // TODO: make simplification of the instantiated formula explicit?
        val instFor =
          CertFormula(quantifiedFormula.toConj.instantiate(instanceTerms)(order))
        val terms =
          "(" + instanceTerms.map(term2String).mkString(" ") + ")"
        val l1 =
          introduceFormulaThroughResolution("forall_inst",
                                            List(quantifiedFormula),
                                            instFor,
                                            swapOrder = true,
                                            useOr = true,
                                            extraAttributes = List(("args", terms)))
        val l2 =
          disjunctionToClause(instFor, l1)
        hyperResolution(instFor, dischargedAtoms, result)
      }
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
