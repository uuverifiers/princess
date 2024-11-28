/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
 *               2020-2021 Zafer Esen <zafer.esen@gmail.com>
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

package ap.parser

import ap._
import ap.basetypes.IdealInt
import ap.theories._
import ap.theories.strings.StringTheory
import ap.theories.rationals.Rationals
import ap.theories.bitvectors.ModPostprocessor
import ap.theories.sequences.SeqTheory
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parser.IExpression.Quantifier
import IExpression.Sort
import ap.types.{SortedIFunction, SortedPredicate, MonoSortedIFunction,
                 SortedConstantTerm, MonoSortedPredicate,
                 UninterpretedSortTheory}
import ap.util.{Seqs, Debug}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 HashSet => MHashSet, LinkedHashMap}

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the SMT-LIB 2 format
 */
object SMTLineariser {

  import SMTTypes._
  import SMTParser2InputAbsy.SMTFunctionType

  private val AC = Debug.AC_PARSER

  private val SaneId =
    """[+-/*=%?!.$_~&^<>@a-zA-Z][+-/*=%?!.$_~&^<>@a-zA-Z0-9]*""".r
  
  def quoteIdentifier(str : String) = str match {
    case SaneId() => str
    case _        => "|" + str.replace("|", "\\|") + "|"
  }

  //////////////////////////////////////////////////////////////////////////////
  // Operations for escapeing/de-escaping SMT-LIB strings

  class IllegalStringException extends Exception("Incorrectly escaped string")

  def unescapeIt(it : Iterator[Int]) : Seq[Int] = {
    var state = 0
    val res = new ArrayBuffer[Int]
    val charBuffer = new ArrayBuffer[Char]

    def parseHex : Unit = {
          if (charBuffer.size > 5)
            throw new IllegalStringException
          res += Integer.parseInt(charBuffer.mkString, 16)
          charBuffer.clear
    }

    def parseOct : Unit = {
          if (charBuffer.size != 3)
            throw new IllegalStringException
          res += Integer.parseInt(charBuffer.mkString, 8)
          charBuffer.clear
    }

    def isOct(c : Int) : Boolean =
          48 <= c && c <= 55

    def isHex(c : Int) : Boolean =
          (48 <= c && c <= 57) ||
          (65 <= c && c <= 70) ||
          (97 <= c && c <= 102)

    while (it.hasNext)
      (state, it.next) match {
        case (0, 92) =>                                   // \
          state = 1
        case (1, 92) => {                                 // \
          res += 92
          state = 0
        }

        case (1, 117) =>                                  // u
          state = 2

        // C++-style escape sequences. Add \e?
        case (1, c@(97 | 98 | 102)) => {                  // a, b, f
          res += c - 90
          state = 0
        }
        case (1, 110) => {                                // n
          res += 10
          state = 0
        }
        case (1, 114) => {                                // r
          res += 13
          state = 0
        }
        case (1, 116) => {                                // t
          res += 9
          state = 0
        }
        case (1, 118) => {                                // v
          res += 11
          state = 0
        }

        case (2, 123) =>                                  // {
          state = 3
        case (2, c) if isHex(c) => {                      // [0-9a-fA-F]
          charBuffer += c.toChar
          state = 7
        }
        case (3, c) if isHex(c) =>                        // [0-9a-fA-F]
          charBuffer += c.toChar
        case (3, 125) => {                                // }
          parseHex
          state = 0
        }

        case (1, 120) =>                                  // x
          state = 6
        case (6, c) if isHex(c) => {                      // [0-9a-fA-F]
          charBuffer += c.toChar
          state = 7
        }
        case (7, c) if isHex(c) => {                      // [0-9a-fA-F]
          charBuffer += c.toChar
          parseHex
          state = 0
        }

        case (1, c) if isOct(c) => {                      // [0-7]
          charBuffer += c.toChar
          state = 8
        }
        case (8, c) if isOct(c) => {                      // [0-7]
          charBuffer += c.toChar
          state = 9
        }
        case (9, c) if isOct(c) => {                      // [0-7]
          charBuffer += c.toChar
          parseOct
          state = 0
        }

        case (0, 34) =>                                   // "
          state = 20
        case (20, 34) => {                                // "
          state = 0
          res += 34
        }

        case (0, c) =>
          res += c

        case (1, 34) => {                                 // "
          // then we have already seen a \
          state = 20
          res += 92
        }

        case (1, c) => {
          // then we have already seen a \
          state = 0
          res += 92
          res += c
        }

        case _ =>
          throw new IllegalStringException
      }

    state match {
      case 0 =>
        // ok
      case 1 =>
        // then we have already seen a \
        res += 92
      case _ =>
        throw new IllegalStringException
    }

    res
  }

  /**
   * Unescaping strictly following the SMT-LIB standard.
   */
  def simpleUnescapeIt(it : Iterator[Int]) : Seq[Int] = {
    var state = 0
    val res = new ArrayBuffer[Int]
    val charBuffer = new ArrayBuffer[Char]

    def parseHex : Unit = {
      if (charBuffer.size > 5)
        throw new IllegalStringException
      res += Integer.parseInt(charBuffer.mkString, 16)
      charBuffer.clear
    }

    def isHex(c : Int) : Boolean =
      (48 <= c && c <= 57) ||
      (65 <= c && c <= 70) ||
      (97 <= c && c <= 102)

    while (it.hasNext)
      (state, it.next) match {
        case (0, 92) =>                                   // \
          state = 1

        case (1, 117) =>                                  // u
          state = 2

        case (2, 123) =>                                  // {
          state = 3
        case (2, c) if isHex(c) => {                      // [0-9a-fA-F]
          charBuffer += c.toChar
          state = 7
        }
        case (3, c) if isHex(c) =>                        // [0-9a-fA-F]
          charBuffer += c.toChar
        case (3, 125) => {                                // }
          parseHex
          state = 0
        }

        case (7, c) if isHex(c) => {                      // [0-9a-fA-F]
          charBuffer += c.toChar
          parseHex
          state = 0
        }

        case (0, 34) =>                                   // "
          state = 20
        case (20, 34) => {                                // "
          state = 0
          res += 34
        }

        case (0, c) =>
          res += c

        case (1, 34) => {                                 // "
          // then we have already seen a \
          state = 20
          res += 92
        }

        case (1, c) => {
          // then we have already seen a \
          state = 0
          res += 92
          res += c
        }

        case _ =>
          throw new IllegalStringException
      }

    state match {
      case 0 =>
        // ok
      case 1 =>
        // then we have already seen a \
        res += 92
      case _ =>
        throw new IllegalStringException
    }

    res
  }

  private def escapeChar(c: Int): String = c match {
    case 34 =>
      "\"\""
    case c if c >= 32 && c <= 126 && c != 92 =>
      "" + c.toChar
    case c =>
      "\\u{" + Integer.toString(c, 16) + "}"
  }

  def escapeString(str : String) : String =
    for (c <- str; d <- escapeChar(c)) yield d

  def unescapeString(str : String) : String =
    (unescapeIt(str.iterator map (_.toInt)) map (_.toChar)).mkString

  /**
   * Unescape a single-quoted string; the only recognised escape
   * sequence is ''
   */
  def escapeSQString(str : String) : String =
    str.replace("'", "''")

  /**
   * Unescape a single-quoted string; the only recognised escape
   * sequence is ''
   */
  def unescapeSQString(str : String) : String =
    str.replace("''", "'")

  //////////////////////////////////////////////////////////////////////////////

  def toSMTExpr(value : IdealInt) : String =
    if (value.signum < 0)
      "(- " + value.abs.toString + ")"
    else
      value.toString
  
  def printModel(model : IFormula) : Unit = {
    import IExpression._
    import Sort.:::

    println("(model")

    def printEq(lhs : ConstantTerm, sort : Sort, rhs : ITerm) : Unit = {
      print("  (define-fun " + quoteIdentifier(lhs.name) + " () ")
      printSMTType(sort2SMTType(sort)._1)
      print(" ")
      apply(rhs)
      println(")")
    }

    val funPoints =
      new LinkedHashMap[IFunction, ArrayBuffer[(Seq[ITerm], ITerm)]]
    val predPoints =
      new LinkedHashMap[Predicate, ArrayBuffer[(Seq[ITerm], Boolean)]]

    for (conj <- LineariseVisitor(model, IBinJunctor.And)) conj match {
      case Eq(IConstant(c) ::: sort, t) =>
        printEq(c, sort, t)
      case Eq(t, IConstant(c) ::: sort) =>
        printEq(c, sort, t)
      case Eq(IFunApp(f, args), t)
          if (TheoryRegistry lookupSymbol f).isEmpty =>
        funPoints.getOrElseUpdate(f, new ArrayBuffer) += ((args, t))
      case Eq(t, IFunApp(f, args))
          if (TheoryRegistry lookupSymbol f).isEmpty =>
        funPoints.getOrElseUpdate(f, new ArrayBuffer) += ((args, t))
      case IAtom(p, Seq()) =>
        println("  (define-fun " + quoteIdentifier(p.name) + " () Bool true)")
      case INot(IAtom(p, Seq())) =>
        println("  (define-fun " + quoteIdentifier(p.name) + " () Bool false)")
      case IAtom(p, args) =>
        predPoints.getOrElseUpdate(p, new ArrayBuffer) += ((args, true))
      case INot(IAtom(p, args)) =>
        predPoints.getOrElseUpdate(p, new ArrayBuffer) += ((args, false))
      case IBoolLit(true) =>
        // can be ignored, empty model
    }

    for ((f, points) <- funPoints) {
      val ft@(argSorts, resSort) =
        SortedIFunction.iFunctionType(f, points.head._1)
      val formalArgs =
        for ((s, n) <- argSorts.zipWithIndex) yield (s newConstant ("x!" + n))
      val default =
        resSort.witness getOrElse i(0)
      val body =
        (default /: points) {
          case (ob, (args, result)) => ite(formalArgs === args, result, ob)
        }
      print("  ")
      printDefineFun(f, ft, formalArgs, body)
    }

    for ((p, points) <- predPoints) {
      val argSorts =
        SortedPredicate.iArgumentSorts(p, points.head._1)
      val formalArgs =
        for ((s, n) <- argSorts.zipWithIndex) yield (s newConstant ("x!" + n))
      val body =
        or(for ((args, true) <- points.iterator) yield (formalArgs === args))
      print("  ")
      printDefineFun(new IFunction(p.name, p.arity, false, false),
                     (argSorts, Sort.Bool), formalArgs, body)
    }

    println(")")
  }

  def printDefineFun(f : IFunction,
                     functionType : (Seq[Sort], Sort),
                     formalArgs : Seq[ConstantTerm],
                     body : IExpression) : Unit = {
    val (argSorts, resSort) = functionType
    print("(define-fun " + quoteIdentifier(f.name) + " ")
    printArguments(argSorts, formalArgs)
    print(" ")
    printSMTType(sort2SMTType(resSort)._1)
    print(" ")
    apply(body)
    println(")")
  }

  def printArguments(argSorts : Seq[Sort],
                     formalArgs : Seq[ConstantTerm]) : Unit = {
    print("(")
    var sep = ""
    for ((a, t) <- formalArgs.iterator zip argSorts.iterator) {
      print(sep)
      sep = " "
      print("(")
      print(quoteIdentifier(a.name))
      print(" ")
      printSMTType(sort2SMTType(t)._1)
      print(")")
    }
    print(")")
  }

  //////////////////////////////////////////////////////////////////////////////

  private val constantTypeFromSort =
    (c : ConstantTerm) => Some(sort2SMTType(SortedConstantTerm sortOf c)._1)

  val functionTypeFromSort =
    (f : IFunction) => f match {
      case f : MonoSortedIFunction =>
        Some(SMTFunctionType(
               (f.argSorts map { s => sort2SMTType(s)._1 }).toList,
               sort2SMTType(f.resSort)._1))
      case _ : SortedIFunction =>
        None
      case _ : IFunction =>
        Some(SMTFunctionType(
               (for (_ <- 0 until f.arity) yield SMTInteger).toList,
               SMTInteger))
    }

  val predTypeFromSort =
    (p : Predicate) => p match {
      case p : MonoSortedPredicate =>
        Some(SMTFunctionType(
               (p.argSorts map { s => sort2SMTType(s)._1 }).toList,
               SMTBool))
      case _ : SortedPredicate =>
        None
      case _ : Predicate =>
        Some(SMTFunctionType(
               (for (_ <- 0 until p.arity) yield SMTInteger).toList,
               SMTBool))
    }

  private val trueConstant  = IConstant(Sort.Bool newConstant "true")
  private val falseConstant = IConstant(Sort.Bool newConstant "false")
  private val eqPredicate   = new Predicate ("=", 2)

  private val invisible1    = new IFunction("", 1, true, false)
  private val invisible2    = new IFunction("", 2, true, false)

  //////////////////////////////////////////////////////////////////////////////

  def printSMTType(t : SMTType) : Unit =
    print(t.toSMTLIBString)

  def smtTypeAsString(t : SMTType) : String =
    t.toSMTLIBString

  def sort2SMTType(sort : Sort) : (SMTType, Option[ITerm => IFormula]) =
    SMTTypes.sort2SMTType(sort)

  def sort2SMTString(sort : Sort) : String =
    smtTypeAsString(sort2SMTType(sort)._1)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Topologically sort theories to be declared: dependencies of a
   * theory preceed the theory in the resulting list.
   */
  def sortTheoryDeps(theories : Seq[Theory]) : Seq[Theory] = {
    val undeclaredTheories = new MHashSet[Theory]
    undeclaredTheories ++= theories

    val res = new ArrayBuffer[Theory]
    var remainingTheories : Seq[Theory] = theories

    while (!remainingTheories.isEmpty) {
      val (decl, rem) = remainingTheories.partition {
        t => Seqs.disjointSeq(undeclaredTheories, t.transitiveDependencies)
      }

      if (rem.size == remainingTheories.size)
        throw new IllegalArgumentException(
          "cyclic dependencies during theory declaration")

      remainingTheories = rem
      res ++= decl

      undeclaredTheories --= decl
    }

    val subsumedTheories = new MHashSet[Theory]
    for ((t, n) <- res.toList.zipWithIndex.reverseIterator)
      if (subsumedTheories contains t) {
        res.remove(n)
      } else if (t.isInstanceOf[SMTLinearisableTheory]) {
        subsumedTheories ++=
          t.asInstanceOf[SMTLinearisableTheory].SMTDeclarationSideEffects
      }

    res.toSeq
  }

  //////////////////////////////////////////////////////////////////////////////

  def apply(expr : IExpression) : Unit = expr match {
    case f : IFormula => apply(f)
    case t : ITerm =>    apply(t)
  }

  def apply(formula : IFormula) : Unit =
    apply(formula, constantTypeFromSort, functionTypeFromSort, predTypeFromSort)

  def applyNoPrettyBitvectors(formula : IFormula) : Unit =
    apply(formula, constantTypeFromSort, functionTypeFromSort, predTypeFromSort,
          false)

  def apply(formula : IFormula,
            constantType :
              ConstantTerm => Option[SMTTypes.SMTType],
            functionType :
              IFunction => Option[SMTParser2InputAbsy.SMTFunctionType],
            predType :
              Predicate => Option[SMTParser2InputAbsy.SMTFunctionType],
            prettyBitvectors : Boolean = true) : Unit =
    formula match {
      case IBoolLit(value) => print(value)
      case _ => {
        val lineariser =
          new SMTLineariser("", "", "", List(), List(), List(), List(),
                            "", "", "",
                            constantType, functionType, predType,
                            prettyBitvectors)
        lineariser printFormula formula
      }
    }

  def apply(term : ITerm) : Unit = {
    val lineariser =
      new SMTLineariser("", "", "", List(), List(), List(), List(),
                        "", "", "",
                        constantTypeFromSort,
                        functionTypeFromSort, predTypeFromSort)
    lineariser printTerm term
  }

  def applyNoPrettyBitvectors(term : ITerm) : Unit = {
    val lineariser =
      new SMTLineariser("", "", "", List(), List(), List(), List(),
                        "", "", "",
                        constantTypeFromSort,
                        functionTypeFromSort, predTypeFromSort,
                        false)
    lineariser printTerm term
  }

  def asString(t : IExpression) : String = t match {
    case t : IFormula => asString(t)
    case t : ITerm => asString(t)
  }

  def asString(formula : IFormula) : String =
    ap.DialogUtil.asString { apply(formula) }

  def asString(t : ITerm) : String =
    ap.DialogUtil.asString { apply(t) }

  //////////////////////////////////////////////////////////////////////////////

  private def findTheories(formulas      : Iterable[IFormula],
                           consts        : Iterable[ConstantTerm],
                           preds         : Iterable[Predicate],
                           funs          : Iterable[IFunction],
                           extraTheories : Iterable[Theory]) : Seq[Theory] = {
    val theoryCollector = new TheoryCollector

    for (t <- extraTheories)
      theoryCollector addTheory t
    
    for (f <- formulas)
      theoryCollector(f)

    for (c <- consts)
      theoryCollector(SortedConstantTerm sortOf c)

    for (p <- preds)
      for (s <- MonoSortedPredicate.argumentSorts(p))
        theoryCollector(s)

    for (f <- funs) {
      val (argSorts, resSort) = MonoSortedIFunction.functionType(f)
      theoryCollector(resSort)
      for (s <- argSorts)
        theoryCollector(s)
    }

    (theoryCollector.theories ++
       (for (t <- theoryCollector.theories;
             s <- t.transitiveDependencies) yield s)).distinct
  }

  //////////////////////////////////////////////////////////////////////////////

  def printWithDeclsSig(formulas      : Seq[IFormula],
                        signature     : Signature,
   		        extraTheories : Seq[Theory] = List(),
                        benchmarkName : String = "",
                        logic         : String = "AUFLIA",
		        status        : String = "unknown") : Unit = {
    val order = signature.order
    
    val (finalFormulas, constsToDeclare) : (Seq[IFormula], Set[ConstantTerm]) =
      if (Seqs.disjoint(order.orderedConstants, signature.existentialConstants)) {
        // if all constants are universal, we do not have to add explicit quantifiers
        (for (f <- formulas) yield ~f,
         signature.universalConstants ++ signature.nullaryFunctions)
      } else {
        val formula = IExpression.connect(formulas, IBinJunctor.Or)
        // add the nullary functions
        val withFunctions =
          IExpression.quanConsts(Quantifier.ALL, signature.nullaryFunctions, formula)
        // ... and the existentially quantified constants
        val withExConstants =
          IExpression.quanConsts(Quantifier.EX,
                                 signature.existentialConstants,
                                 withFunctions)
        // add the universally quantified constants
        val withUniConstants =
          IExpression.quanConsts(Quantifier.ALL,
                                 signature.universalConstants,
                                 withFunctions)
        
        (List(~withUniConstants), Set())
      }

    val predsToDeclare =
      for (p <- order.orderedPredicates.toList;
           if (TheoryRegistry lookupSymbol p).isEmpty)
      yield p

    val funsToDeclare = {
      val raw = (for (formula <- finalFormulas.iterator;
                      fun <- FunctionCollector(formula).iterator;
                      if (TheoryRegistry lookupSymbol fun).isEmpty)
		 yield fun).toSet
      raw.toVector.sortBy(_.name)
    }

    val theories = findTheories(finalFormulas,
                                constsToDeclare,
		                predsToDeclare,
	                        funsToDeclare,
                                extraTheories)

    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
                                       constsToDeclare.toList,
                                       predsToDeclare,
				       funsToDeclare,
                                       theories,
                                       "", "", "",
                                       constantTypeFromSort,
                                       functionTypeFromSort,
                                       predTypeFromSort)
   
    lineariser.open
    for (f <- finalFormulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }

  def printWithDecls(formulas        : Seq[IFormula],
                     constsToDeclare : Seq[ConstantTerm] = List(),
                     predsToDeclare  : Seq[Predicate]    = List(),
	             funsToDeclare   : Seq[IFunction]    = List(),
		     extraTheories   : Seq[Theory]       = List(),
	             benchmarkName   : String            = "",
                     logic           : String            = "AUFLIA",
                     status          : String            = "unknown") : Unit = {
    val theories = findTheories(formulas,
                                constsToDeclare,
		                predsToDeclare,
	                        funsToDeclare,
                                extraTheories)
    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
                                       constsToDeclare,
                                       predsToDeclare,
				       funsToDeclare,
                                       theories,
                                       "", "", "",
                                       constantTypeFromSort,
                                       functionTypeFromSort,
                                       predTypeFromSort)
   
    lineariser.open
    for (f <- formulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }

  //////////////////////////////////////////////////////////////////////////////

  private def theoryFun2Identifier(fun : IFunction) : Option[(String, String)] =
    (TheoryRegistry lookupSymbol fun) match {
      case Some(t : SimpleArray) => fun match {
        case t.select => Some(("select", ""))
        case t.store  => Some(("store", ""))
      }
      case Some(t : ExtArray) => fun match {
        case t.select           => Some(("select", ""))
        case t.store            => Some(("store", ""))
        case fun                => Some((fun.name, ""))
      }
      case Some(t : MulTheory) => fun match {
        case t.mul => Some(("*", ""))
      }
      case Some(t : ADT)
        if t.termSize != null && (t.termSize contains fun) =>
        Some(("_size", ""))
      case Some(t : ADT)
        if t != ADT.BoolADT && (t.constructors contains fun) => {
          val monoFun = fun.asInstanceOf[MonoSortedIFunction]
          if (!(monoFun.argSorts contains monoFun.resSort) &&
                (monoFun.resSort.name startsWith SMTADT.POLY_PREFIX)) {
            Some(("(as " + quoteIdentifier(fun.name) + " " +
                    sort2SMTString(monoFun.resSort) +
                    ")", ""))
          } else {
            None
          }
        }
      case Some(Rationals) => fun match {
        case Rationals.frac           => Some(("/", ""))
        case Rationals.fromRing       => Some(("/", "1"))
        case Rationals.addition       => Some(("+", ""))
        case Rationals.multiplication => Some(("*", ""))
        case Rationals.multWithRing   => Some(("*", ""))
        case _                        => None
      }
      case Some(ModuloArithmetic) => fun match {
        case ModuloArithmetic.int_cast => Some(("bv2nat", ""))
        case ModuloArithmetic.bv_add   => Some(("bvadd", ""))
      }
      case Some(DivZero.IntDivZeroTheory) => fun match {
        case DivZero.IntDivZero => Some(("div", "0"))
        case DivZero.IntModZero => Some(("mod", "0"))
      }
      case Some(theory : SeqTheory) => fun match {
        case theory.seq_empty =>
          Some(("(as seq.empty " + sort2SMTString(theory.SeqSort) + ")", ""))
        case _ =>
          Some((fun.name.replace("seq_", "seq."), ""))
      }
      case Some(t : SMTLinearisableTheory) =>
        for (str <- t.fun2SMTString(fun)) yield (str, "")
      case _ =>
        None
    }

  private def theoryPred2Identifier(pred : Predicate) : Option[String] =
    (TheoryRegistry lookupSymbol pred) match {
      case Some(t : SMTLinearisableTheory) =>
        t.pred2SMTString(pred)
      case Some(Rationals) => pred match {
        case Rationals.lessThan        => Some("<")
        case Rationals.lessThanOrEqual => Some("<=")
        case _                         => None
      }
      case _ =>
        None
    }

  private val bvSimpleUnFunction : Map[IFunction, String] = Map(
    ModuloArithmetic.bv_not  -> "bvnot",
    ModuloArithmetic.bv_neg  -> "bvneg"
  )

  private val bvSimpleBinFunction : Map[IFunction, String] = Map(
    ModuloArithmetic.bv_and  -> "bvand",
    ModuloArithmetic.bv_or   -> "bvor",
    ModuloArithmetic.bv_add  -> "bvadd",
    ModuloArithmetic.bv_sub  -> "bvsub",
    ModuloArithmetic.bv_mul  -> "bvmul",
    ModuloArithmetic.bv_udiv -> "bvudiv",
    ModuloArithmetic.bv_sdiv -> "bvsdiv",
    ModuloArithmetic.bv_urem -> "bvurem",
    ModuloArithmetic.bv_srem -> "bvsrem",
    ModuloArithmetic.bv_smod -> "bvsmod",
    ModuloArithmetic.bv_shl  -> "bvshl",
    ModuloArithmetic.bv_lshr -> "bvlshr",
    ModuloArithmetic.bv_ashr -> "bvashr",
    ModuloArithmetic.bv_xor  -> "bvxor",
    ModuloArithmetic.bv_xnor -> "bvxnor",
    ModuloArithmetic.bv_comp -> "bvcomp"
  )

  private val bvSimpleBinPred : Map[Predicate, String] = Map(
    ModuloArithmetic.bv_ult  -> "bvult",
    ModuloArithmetic.bv_ule  -> "bvule",
    ModuloArithmetic.bv_slt  -> "bvslt",
    ModuloArithmetic.bv_sle  -> "bvsle"
  )

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for printing <code>IFormula</code>s in the SMT-Lib format
 */
class SMTLineariser(benchmarkName     : String,
                    logic             : String,
                    status            : String,
                    constsToDeclare   : Seq[ConstantTerm],
                    predsToDeclare    : Seq[Predicate],
                    funsToDeclare     : Seq[IFunction],
                    theoriesToDeclare : Seq[Theory],
                    funPrefix         : String,
                    predPrefix        : String,
                    constPrefix       : String,
                    constantType :
                       ConstantTerm => Option[SMTTypes.SMTType],
                    functionType :
                       IFunction => Option[SMTParser2InputAbsy.SMTFunctionType],
                    predType :
                       Predicate => Option[SMTParser2InputAbsy.SMTFunctionType],
                    prettyBitvectors : Boolean = true) {

  import SMTTypes._
  import SMTLineariser.{quoteIdentifier, toSMTExpr, escapeString,
                        trueConstant, falseConstant, eqPredicate,
                        printSMTType, sortTheoryDeps,
                        sort2SMTString, sort2SMTType, theoryFun2Identifier,
                        theoryPred2Identifier,
                        bvSimpleUnFunction, bvSimpleBinFunction,
                        bvSimpleBinPred, invisible1, invisible2}

  //////////////////////////////////////////////////////////////////////////////

  private def pred2Identifier(pred : Predicate) =
    if (pred == eqPredicate) {
       "="
    } else {
      theoryPred2Identifier(pred) getOrElse
      quoteIdentifier(predPrefix + pred.name)
    }

  private def const2Identifier(const : ConstantTerm) =
    quoteIdentifier(constPrefix + const.name)
  
  private def fun2Identifier(fun : IFunction) : (String, String) =
    theoryFun2Identifier(fun) getOrElse
    (quoteIdentifier(funPrefix + fun.name), "")

  private def adtTester(t : ITerm, adt : ADT,
                        sortNum : Int, ctorPerSortNum : Int) : IFormula = {
    // insert a dummy predicate to represent the tester
    val testPred =
      new Predicate("is-" + adt.getCtorPerSort(sortNum, ctorPerSortNum).name, 1)
    new IAtom (testPred, List(t))
  }

  def open {
    println("(set-logic " + logic + ")")
    println("(set-info :source |")
    if (benchmarkName != "")
      println("    Benchmark: " + benchmarkName)
    println("    Output by Princess (https://github.com/uuverifiers/princess)")
    println("|)")

    if(status.nonEmpty)
      println("(set-info :status " + status + ")")

    for (t <- sortTheoryDeps(theoriesToDeclare))
      t match {
        case t : SMTLinearisableTheory => t.printSMTDeclaration
        case _                         => // nothing
      }

    // declare the required predicates
    for (pred <- predsToDeclare) {
      val argSorts = MonoSortedPredicate.argumentSorts(pred)
      print("(declare-fun " + pred2Identifier(pred) + " (")
      print((argSorts map (sort2SMTString(_))) mkString " ")
      println(") Bool)")
    }
    
    // declare the required functions
    for (fun <- funsToDeclare) {
      val (argSorts, resSort) = MonoSortedIFunction.functionType(fun)
      print("(declare-fun " + fun2Identifier(fun)._1 + " (")
      print((argSorts map (sort2SMTString(_))) mkString " ")
      println(") " + sort2SMTString(resSort) + ")")
    }
    
    // declare universal constants
    for (const <- constsToDeclare) {
      print("(declare-fun " + const2Identifier(const) + " () ")
      printSMTType(constantType(const) getOrElse SMTTypes.SMTInteger)
      println(")")
    }
  }
  
  def printFormula(clauseName : String, formula : IFormula) {
    print("(" + clauseName + " ")
    printFormula(formula)
    println(")")
  }
  
  def printFormula(formula : IFormula) = {
    // first derive types of variables
    var typedFormula = formula

//    val bitvecFormula = (new BitVectorTranslator).visit(typedFormula, ())
    if (prettyBitvectors)
      typedFormula = ModPostprocessor.purifyFormula(typedFormula)

/*
    var oldTypedFormula : IFormula = null
    while (!(typedFormula eq oldTypedFormula)) {
      oldTypedFormula = typedFormula
      typedFormula =
        VariableTypeInferenceVisitor.visit(typedFormula, ())
                                    .asInstanceOf[IFormula]
    }
 */

    // Make sure that ADT testers have the right form
    typedFormula = ADT.CtorIdRewriter(typedFormula)

    AbsyPrinter(typedFormula)
  }
  
  def printTerm(term : ITerm) =
    AbsyPrinter(term)
  
  def close {
    println("(check-sat)")
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  import SMTParser2InputAbsy.SMTFunctionType

  private def getTermType(t : ITerm)
                         (implicit variableType : Int => Option[SMTType])
                         : Option[SMTType] = t match {
    case IFunApp(SimpleArray.Select(), args) =>
      for (SMTArray(_, res) <- getTermType(args.head)) yield res
    case IFunApp(SimpleArray.Store(), args) =>
      getTermType(args.head)
    case IFunApp(f, _) =>
      for (SMTFunctionType(_, res) <- functionType(f)) yield res
    case IConstant(c) =>
      constantType(c)
    case IVariable(ind) =>
      variableType(ind)
    case _ => None
  }

  private def getArgTypes(t : IFunApp)
                         (implicit variableType : Int => Option[SMTType])
                         : Option[Seq[SMTType]] = {
    val IFunApp(fun, args) = t
    fun match {
      case SimpleArray.Select() =>
        for (s@SMTArray(argTypes, _) <- getTermType(args.head))
        yield (s :: argTypes)
      case SimpleArray.Store() =>
        for (s@SMTArray(argTypes, resType) <- getTermType(args.head))
        yield (s :: argTypes ::: List(resType))
      case fun =>
        for (SMTFunctionType(argTypes, _) <- functionType(fun)) yield argTypes
    }
  }

  private def getArgTypes(t : IAtom) : Option[Seq[SMTType]] = {
    val IAtom(pred, args) = t
    for (SMTFunctionType(argTypes, _) <- predType(pred)) yield argTypes
  }

  private object BooleanTerm {
    def unapply(t : IExpression)
               (implicit variableType : Int => Option[SMTType])
               : Option[ITerm] = t match {
      case t@IFunApp(f, _)
        if (functionType(f) match {
              case Some(SMTFunctionType(_, SMTBool)) => true
              case _ => false
            }) =>
        Some(t)
      case t : ITerm if (getTermType(t) == Some(SMTBool)) =>
        Some(t)
      case _ =>
        None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private case class PrintContext(vars : List[(String, Option[SMTType])],
                                  parentOp : String) {
    def pushVar(name : String, t : Option[SMTType] = None, op : String = "") =
      PrintContext((name, t) :: vars, op)
    def setParentOp(op : String) = PrintContext(vars, op)
    def addParentOp(op : String) = PrintContext(vars, op + parentOp)
    implicit val variableType : Int => Option[SMTType] = (ind) => vars(ind)._2
  }

  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {
    def apply(e : IExpression) : Unit = {
//      spaceSkipped = false
      visitWithoutResult(e, PrintContext(List(), ""))
    }

    private def shortCut(ctxt : PrintContext) = {
      print(ctxt.parentOp)
      ShortCutResult(())
    }

    private def noParentOp(ctxt : PrintContext) =
      UniSubArgs(ctxt setParentOp "")
    private def addParentOp(ctxt : PrintContext, op : String) =
      UniSubArgs(ctxt addParentOp op)

    private def allButLast(ctxt : PrintContext, op : String, lastOp : String,
                           arity : Int) = {
      val newCtxt = ctxt setParentOp op
      SubArgs((for (_ <- 1 until arity) yield newCtxt) ++
                List(ctxt setParentOp lastOp))
    }

    private def closeWithParen(ctxt : PrintContext, arity : Int = 1) =
      allButLast(ctxt, " ", ")", arity)

    override def preVisit(t : IExpression,
                          ctxt : PrintContext) : PreVisitResult = {
    import ctxt.variableType
    t match {
      // Terms
      case IConstant(c) => {
        print(const2Identifier(c))
        shortCut(ctxt)
      }
      case IIntLit(value) => {
        print(toSMTExpr(value))
        shortCut(ctxt)
      }
      case IPlus(_, _) => {
        print("(+ ")
        closeWithParen(ctxt, 2)
      }
      case ITimes(coeff, _) => {
        print("(* " + toSMTExpr(coeff) + " ")
        closeWithParen(ctxt)
      }
      case IVariable(index) => {
        print(ctxt.vars(index)._1)
        shortCut(ctxt)
      }
      
      case IFunApp(`invisible1`, _) => {
        print(" ")
        closeWithParen(ctxt, 1)
      }

      case IFunApp(`invisible2`, _) => {
        print(" ")
        closeWithParen(ctxt, 2)
      }

      //////////////////////////////////////////////////////////////////////////
      // Bit-vectors

      case IFunApp(f, Seq(_, arg1)) if bvSimpleUnFunction contains f => {
        print("(")
        print(bvSimpleUnFunction(f))
        TryAgain(IFunApp(invisible1, List(arg1)), ctxt)
      }

      case IFunApp(f, Seq(_, arg1, arg2)) if bvSimpleBinFunction contains f => {
        print("(")
        print(bvSimpleBinFunction(f))
        TryAgain(IFunApp(invisible2, List(arg1, arg2)), ctxt)
      }

      case IAtom(p, Seq(_, arg1, arg2)) if bvSimpleBinPred contains p => {
        print("(")
        print(bvSimpleBinPred(p))
        TryAgain(IFunApp(invisible2, List(arg1, arg2)), ctxt)
      }

      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO), IIntLit(upper),
                       IIntLit(value)))
          if prettyBitvectors && (upper & (upper + 1)).isZero => {
        print("(_ bv" + (value % (upper + 1)) + " " +
              (upper.getHighestSetBit + 1) + ")")
        shortCut(ctxt)
      }

      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO), IIntLit(card),
                       IIntLit(value)))
          if prettyBitvectors => {
        print("(as ff" + (value % (card + 1)) + " " +
              "(_ FiniteField " + (card + 1) + "))")
        shortCut(ctxt)
      }

      case IFunApp(ModuloArithmetic.bv_extract,
                   Seq(IIntLit(upper), IIntLit(lower), arg)) => {
        print("((_ extract " + upper + " " + lower + ") ")
        TryAgain(arg, ctxt addParentOp ")")
      }

      case IFunApp(ModuloArithmetic.bv_concat,
                   Seq(_, _, arg1, arg2)) => {
        print("(concat")
        TryAgain(IFunApp(invisible2, List(arg1, arg2)), ctxt)
      }

      case IFunApp(ModuloArithmetic.zero_extend,
                   Seq(IIntLit(_), IIntLit(addWidth), arg)) => {
        print("((_ zero_extend " + addWidth + ") ")
        TryAgain(arg, ctxt addParentOp ")")
      }

      //////////////////////////////////////////////////////////////////////////

      case StringTheory.ConcreteString(str) => {
        print("\"")
        print(escapeString(str))
        print("\"")
        shortCut(ctxt)
      }

      case IFunApp(ExtArray.Const(t), Seq(value)) => {
        print("((as const " + sort2SMTString(t.sort) + ") ")
        TryAgain(value, ctxt addParentOp ")")
      }

      //////////////////////////////////////////////////////////////////////////

      case t@IFunApp(fun, args) => {
        // check if any Boolean arguments have to be decoded
        var changed = false
        val newArgs = getArgTypes(t) match {
          case Some(argTypes) =>
            (for (p <- args.iterator zip argTypes.iterator) yield p match {
               case (IIntLit(IdealInt.ZERO), SMTBool) => {
                 changed = true
                 trueConstant
               }                
               case (IIntLit(v), SMTBool) if (!v.isZero) => {
                 changed = true
                 falseConstant
               }
               case (t, _) => t
             }).toList
          case _ => args
        }

        if (changed) {
          TryAgain(IFunApp(fun, newArgs), ctxt)
        } else if (args.isEmpty) {
          print(fun2Identifier(fun)._1)
          shortCut(ctxt)
        } else {
          val (prefix, suffix) = fun2Identifier(fun)
          print("(" + prefix + " ")
          allButLast(ctxt, " ",
                     if (suffix == "") ")" else (" " + suffix + ")"),
                     args.size)
        }
      }

      case _ : ITermITE | _ : IFormulaITE => {
        print("(ite ")
        closeWithParen(ctxt, 3)
      }

      // Formulae
      case IAtom(pred, args) =>
        if (args.isEmpty) {
          print(pred2Identifier(pred))
          shortCut(ctxt)
        } else {
          print("(" + pred2Identifier(pred) + " ")
          closeWithParen(ctxt, args.size)
        }

      case IBinFormula(junctor, _, _) => {
        print("(")
        print(junctor match {
          case IBinJunctor.And => "and"
          case IBinJunctor.Or => "or"
          case IBinJunctor.Eqv => "="
        })
        print(" ")
        closeWithParen(ctxt, 2)
      }
      case IBoolLit(value) => {
        print(value)
        shortCut(ctxt)
      }

      // Terms with Boolean type, which were encoded as integer terms or
      // using ADTs
      case IExpression.EqLit(BooleanTerm(t), v) =>
        // strip off the integer encoding
        if (v.isZero)
          TryAgain(t, ctxt)
        else
          TryAgain(!IExpression.eqZero(t), ctxt)

      case IExpression.Eq(ADT.BoolADT.True, t) =>
        // strip off the ADT encoding
        TryAgain(t, ctxt)
      case IExpression.Eq(t, ADT.BoolADT.True) =>
        // strip off the ADT encoding
        TryAgain(t, ctxt)
      case IExpression.Eq(ADT.BoolADT.False, t) => {
        // strip off the ADT encoding
        print("(not ")
        TryAgain(t, ctxt addParentOp ")")
      }
      case IExpression.Eq(t, ADT.BoolADT.False) => {
        // strip off the ADT encoding
        print("(not ")
        TryAgain(t, ctxt addParentOp ")")
      }

      // ADT expression
      case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)), num)=>
        TryAgain(adtTester(arg, adt, sortNum, num.intValueSafe), ctxt)

      // General equations
      case x@IExpression.Eq(s, t) =>
        // rewrite to a proper equation
        TryAgain(IAtom(eqPredicate, List(s, t)), ctxt)
      case IIntFormula(rel, _) => {
        print("(")
        print(rel match {
          case IIntRelation.EqZero => "="
          case IIntRelation.GeqZero => "<="
        })
        print(" 0 ")
        closeWithParen(ctxt)
      }
      case INot(_) => {
        print("(not ")
        closeWithParen(ctxt)
      }

      case f@IQuantified(quan, _) => {
        quan match {
          case Quantifier.ALL => print("(forall (")
          case Quantifier.EX  => print("(exists (")
        }

        var curCtxt = ctxt
        var curF : IFormula = f
        var sep = ""

        def pushVar(t : SMTType) = {
          val varName = "var" + curCtxt.vars.size
          curCtxt = curCtxt.pushVar(varName, Some(t), curCtxt.parentOp)
          print(sep + "(" + varName + " ")
          printSMTType(t)
          print(")")
          sep = " "
        }

        var cont = true
        while (cont) curF match {
          case ISortedQuantified(`quan`, sort, g) => {
            pushVar(sort2SMTType(sort)._1)
            curF = g
          }
          case _ => {
            cont = false
          }
        }

        print(") ")
        TryAgain(curF, curCtxt addParentOp ")")
      }

      // Euclidian integer division can be translated to "div"
      case IEpsilon(IExpression.Conj(
           IExpression.Geq(num1, ITimes(denom1, IVariable(0))),
           IExpression.Geq(IExpression.Difference(ITimes(denom2, IVariable(0)),
                             IExpression.Difference(num2, IIntLit(denom3))),
               IIntLit(IdealInt.ONE))
           ))
         if (num1 == num2 && denom1 == denom2 && denom2.abs == denom3 &&
             ContainsSymbol.freeFromVariableIndex(num1, Set(0))) => {
        print("(div ")
        visit(VariableShiftVisitor(num1, 1, -1), ctxt)
        print(" " + toSMTExpr(denom1) + ")")
        shortCut(ctxt)
      }

      // Euclidian modulo can be translated to "mod"
      case IEpsilon(IExpression.Conj(IExpression.Conj(
           IExpression.GeqZ(IVariable(0)),
           IExpression.Geq(IExpression.Difference(IIntLit(denom1),IVariable(0)),
                           IIntLit(IdealInt.ONE))),
           IQuantified(Quantifier.EX,
                       IExpression.Eq(num, IPlus(
                              ITimes(denom2, IVariable(0)), IVariable(1))))))
         if (ContainsSymbol.freeFromVariableIndex(num, Set(0, 1)) &&
             denom1 == denom2.abs) => {
        print("(mod ")
        visit(VariableShiftVisitor(num, 2, -2), ctxt)
        print(" " + toSMTExpr(denom2) + ")")
        shortCut(ctxt)
      }

      case ISortedEpsilon(sort, f) => {
        val varName = "var" + ctxt.vars.size
        print("(_eps ((" + varName + " ")
        val (t, None) = sort2SMTType(sort)
        printSMTType(t)
        print(")) ")
        TryAgain(f, ctxt.pushVar(varName, Some(t), ")" + ctxt.parentOp))
      }

      case ITrigger(trigs, body) => {
        // we have to handle this case recursively, since the
        // order of the parameters has to be changed
        
        print("(! ")
        visit(body, ctxt)
        print(" :pattern (")
        for (t <- trigs)
          visit(t, ctxt)
        print("))")
        
        shortCut(ctxt)
      }
    }
    }
    
    def postVisit(t : IExpression,
                  arg : PrintContext, subres : Seq[Unit]) : Unit =
      print(arg.parentOp)
  
  }
  
}

