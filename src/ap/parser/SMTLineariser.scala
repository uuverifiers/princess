/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap._
import ap.basetypes.IdealInt
import ap.theories._
import ap.theories.strings.StringTheory
import ap.theories.rationals.Rationals
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parser.IExpression.Quantifier
import IExpression.Sort
import ap.types.{SortedIFunction, SortedPredicate, MonoSortedIFunction,
                 SortedConstantTerm, MonoSortedPredicate,
                 UninterpretedSortTheory}
import ap.util.{Seqs, Debug}

import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 HashSet => MHashSet, LinkedHashMap}

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the SMT-LIB 2 format
 */
object SMTLineariser {

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
    val res = new VectorBuilder[Int]
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

        case (1, c) => {
          // then we have already seen a \
          state = 0
          res += 92
          res += c
        }

//        case _ =>
///          throw new IllegalStringException
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

    res.result
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

  import SMTParser2InputAbsy.{SMTType, SMTArray, SMTBool, SMTInteger, SMTReal,
                              SMTBitVec, SMTString, SMTFunctionType, SMTUnint,
                              SMTADT}

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

  private val bvadd = new IFunction("bvadd", 2, true, true)
  private val bvmul = new IFunction("bvmul", 2, true, true)
  private val bvneg = new IFunction("bvneg", 1, true, true)
  private val bvuge = new Predicate("bvuge", 2)
  private val bvsge = new Predicate("bvsge", 2)

  //////////////////////////////////////////////////////////////////////////////

  def printSMTType(t : SMTType) : Unit = t match {
    case SMTInteger          => print("Int")
    case SMTBool             => print("Bool")
    case SMTReal(_)          => print("Real")
    case t : SMTADT          => print(quoteIdentifier(t.toString))
    case SMTBitVec(width)    => print("(_ BitVec " + width + ")")
    case SMTString(_)        => print("String")
    case SMTArray(args, res) => {
      print("(Array")
      for (s <- args) {
        print(" ")
        printSMTType(s)
      }
      print(" ")
      printSMTType(res)
      print(")")
    }
    case SMTUnint(sort)      => print(sort)
  }

  def smtTypeAsString(t : SMTType) : String =
    DialogUtil asString { printSMTType(t) }

  def sort2SMTType(sort : Sort) : (SMTType,
                                   Option[ITerm => IFormula]) = sort match {
    case Sort.Integer =>
      (SMTInteger, None)
    case Sort.Nat =>
      (SMTInteger, Some(_ >= 0))
    case sort : Sort.Interval =>
      (SMTInteger, Some(sort.membershipConstraint _))
    case Sort.Bool | Sort.MultipleValueBool =>
      (SMTBool, None)
    case sort if (StringTheory lookupStringSort sort).isDefined =>
      (SMTString(sort), None)
    case sort : ADT.ADTProxySort =>
      (SMTADT(sort.adtTheory, sort.sortNum), None)
    case ModuloArithmetic.UnsignedBVSort(width) =>
      (SMTBitVec(width), None)
    case SimpleArray.ArraySort(arity) =>
      (SMTArray((for (_ <- 0 until arity) yield SMTInteger).toList, SMTInteger),
       None)
    case Rationals.FractionSort =>
      (SMTReal(sort), None)
    case sort : UninterpretedSortTheory.UninterpretedSort =>
      (SMTUnint(sort), None)
    case sort : UninterpretedSortTheory.InfUninterpretedSort =>
      (SMTUnint(sort), None)
    case Sort.AnySort =>
      (SMTInteger, None)
    case s =>
      throw new Exception (
        "do not know how to translate " + s + " to an SMT-LIB type")
  }

  def sort2SMTString(sort : Sort) : String =
    smtTypeAsString(sort2SMTType(sort)._1)

  //////////////////////////////////////////////////////////////////////////////

  def printADTDeclarations(adts : Seq[ADT]) : Unit = {
    // we need to sort the ADTs, because they might depend on each other
    val allADTs, declaredADTs = new MHashSet[ADT]
    allADTs ++= adts

    while (declaredADTs.size < adts.size) {
      val oldSize = declaredADTs.size

      for (adt <- adts; if !(declaredADTs contains adt)) {
        val allSorts = for (sels <- adt.selectors; f <- sels) yield f.resSort
        if (allSorts forall {
              case s : ADT.ADTProxySort =>
                adt == s.adtTheory ||
                (declaredADTs contains s.adtTheory) ||
                !(allADTs contains s.adtTheory)
              case _ =>
                true
            }) {
          printADTDeclaration(adt)
          declaredADTs += adt
        }
      }

      if (oldSize == declaredADTs.size)
        throw new IllegalArgumentException(
          "Could not sort ADTs due to cyclic dependencies")
    }
  }
  
  def printADTDeclaration(adt : ADT) : Unit =
    if (adt.sorts.size == 1) {
      val sortName = adt.sorts.head.name
      println("(declare-datatype " + quoteIdentifier(sortName) + " (")
      for ((f, sels) <- adt.constructors zip adt.selectors)
        printADTCtor(f, sels)
      println("))")
    } else {
      println("(declare-datatypes (")
      print((for (s <- adt.sorts)
             yield ("(" + quoteIdentifier(s.name) + " 0)")) mkString " ")
      println(") (")
      for (num <- 0 until adt.sorts.size) {
        println("  (")
        for ((f, sels) <- adt.constructors zip adt.selectors;
             if (f.resSort match {
               case s : ADT.ADTProxySort =>
                 s.sortNum == num && s.adtTheory == adt
               case _ =>
                 false
             }))
          printADTCtor(f, sels)
        println("  )")
      }
      println("))")
    }

  private def printADTCtor(ctor : MonoSortedIFunction,
                           selectors : Seq[MonoSortedIFunction]) : Unit = {
    print("  (" + quoteIdentifier(ctor.name))
    for ((s, g) <- ctor.argSorts zip selectors) {
      print(" (" + quoteIdentifier(g.name) + " ")
      printSMTType(sort2SMTType(s)._1)
      print(")")
    }
    println(")")
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
              ConstantTerm => Option[SMTParser2InputAbsy.SMTType],
            functionType :
              IFunction => Option[SMTParser2InputAbsy.SMTFunctionType],
            predType :
              Predicate => Option[SMTParser2InputAbsy.SMTFunctionType],
            prettyBitvectors : Boolean = true) : Unit =
    formula match {
      case IBoolLit(value) => print(value)
      case _ => {
        val lineariser =
          new SMTLineariser("", "", "", List(), List(), List(),
                            "", "", "",
                            constantType, functionType, predType,
                            prettyBitvectors)
        lineariser printFormula formula
      }
    }

  def apply(term : ITerm) : Unit = {
    val lineariser =
      new SMTLineariser("", "", "", List(), List(), List(), "", "", "",
                        constantTypeFromSort,
                        functionTypeFromSort, predTypeFromSort)
    lineariser printTerm term
  }

  def applyNoPrettyBitvectors(term : ITerm) : Unit = {
    val lineariser =
      new SMTLineariser("", "", "", List(), List(), List(), "", "", "",
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

  private def findTheorys(formulas : Iterable[IFormula],
                          consts : Iterable[ConstantTerm],
                          preds : Iterable[Predicate]) : Seq[Theory] = {
    val theoryCollector = new TheoryCollector
    for (f <- formulas)
      theoryCollector(f)

    def checkSort(s : Sort) : Unit = s match {
      case s : ADT.ADTProxySort =>
        theoryCollector addTheory s.adtTheory
      case _ =>
        // nothing
    }

    // also collect ADT types
    for (c <- consts)
      checkSort(SortedConstantTerm sortOf c)

    for (p <- preds) p match {
      case p : MonoSortedPredicate =>
        for (s <- p.argSorts)
          checkSort(s)
      case _ =>
        // nothing
    }

    theoryCollector.theories
  }

  //////////////////////////////////////////////////////////////////////////////

  def apply(formulas : Seq[IFormula], signature : Signature,
            benchmarkName : String) : Unit =
    apply(formulas, signature, "AUFLIA", "unknown", benchmarkName)

  def apply(formulas : Seq[IFormula], signature : Signature,
            logic : String, status : String,
            benchmarkName : String) : Unit = {
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

    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
                                       constsToDeclare.toList,
                                       predsToDeclare,
                                       findTheorys(finalFormulas,
                                                   constsToDeclare,
                                                   predsToDeclare),
                                       "", "", "",
                                       constantTypeFromSort,
                                       functionTypeFromSort,
                                       predTypeFromSort)
   
    lineariser.open
    for (f <- finalFormulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }

  def apply(benchmarkName : String,
            logic : String,
            status : String,
            constsToDeclare : Seq[ConstantTerm],
            predsToDeclare : Seq[Predicate],
            formulas : Seq[IFormula]) : Unit = {
    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
                                       constsToDeclare,
                                       predsToDeclare,
                                       findTheorys(formulas,
                                                   constsToDeclare,
                                                   predsToDeclare),
                                       "", "", "",
                                       constantTypeFromSort,
                                       functionTypeFromSort,
                                       predTypeFromSort)
   
    lineariser.open
    for (f <- formulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for printing <code>IFormula</code>s in the SMT-Lib format
 */
class SMTLineariser(benchmarkName : String,
                    logic : String,
                    status : String,
                    constsToDeclare : Seq[ConstantTerm],
                    predsToDeclare : Seq[Predicate],
                    theoriesToDeclare : Seq[Theory],
                    funPrefix : String, predPrefix : String, constPrefix : String,
                    constantType :
                           ConstantTerm => Option[SMTParser2InputAbsy.SMTType],
                    functionType :
                           IFunction => Option[SMTParser2InputAbsy.SMTFunctionType],
                    predType :
                           Predicate => Option[SMTParser2InputAbsy.SMTFunctionType],
                    prettyBitvectors : Boolean = true) {

  import SMTLineariser.{quoteIdentifier, toSMTExpr, escapeString,
                        trueConstant, falseConstant, eqPredicate,
                        printSMTType, bvadd, bvmul, bvneg, bvuge, bvsge,
                        printADTDeclarations, sort2SMTString}

  private def fun2Identifier(fun : IFunction) =
    (TheoryRegistry lookupSymbol fun) match {
      case Some(t : SimpleArray) => fun match {
        case t.select => "select"
        case t.store => "store"
      }
      case Some(t : MulTheory) => fun match {
        case t.mul => "*"
      }
      case Some(t : ADT)
        if t.termSize != null && (t.termSize contains fun) =>
        "_size"
      case Some(Rationals) if fun == Rationals.frac =>
        "/"
      case Some(ModuloArithmetic) => fun match {
        case ModuloArithmetic.int_cast => "bv2nat"
      }
      case _ =>
        if (zeroExtendFuns contains fun)
          fun.name
        else
          quoteIdentifier(funPrefix + fun.name)
    }

  private def pred2Identifier(pred : Predicate) =
    if (pred == eqPredicate)
       "="
    else
       quoteIdentifier(predPrefix + pred.name)

  private def const2Identifier(const : ConstantTerm) =
    quoteIdentifier(constPrefix + const.name)
  
  private val zeroExtendFunsMap = new MHashMap[Int, IFunction]
  private val zeroExtendFuns    = new MHashSet[IFunction]

  private def getZeroExtend(addedBits : Int) : IFunction =
    zeroExtendFunsMap.getOrElseUpdate(addedBits, {
      val f = new IFunction("(_ zero_extend " + addedBits + ")", 1, true, true)
      zeroExtendFuns += f
      f
    })

  //////////////////////////////////////////////////////////////////////////////

  def open {
    println("(set-logic " + logic + ")")
    println("(set-info :source |")
    println("    Benchmark: " + benchmarkName)
    println("    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("|)")
  
    println("(set-info :status " + status + ")")

    // declare the required theories
    val adts = for (theory <- theoriesToDeclare;
                    if (theory match {
                      case _ : ADT =>
                        true
                      case _ => {
                        Console.err.println("Warning: do not know how to " +
                                            "declare " + theory)
                        false
                      }
                    }))
               yield theory.asInstanceOf[ADT]
    printADTDeclarations(adts)

    // declare the required predicates
    for (pred <- predsToDeclare) {
      print("(declare-fun " + pred2Identifier(pred) + " (")
      
      val argSorts = pred match {
        case pred : MonoSortedPredicate =>
          pred.argSorts
        case _ =>
          for (_ <- 1 to pred.arity) yield Sort.Integer
      }

      print((argSorts map (sort2SMTString(_))) mkString " ")
      println(") Bool)")
    }
    
    // declare universal constants
    for (const <- constsToDeclare) {
      print("(declare-fun " + const2Identifier(const) + " () ")
      printSMTType(constantType(const) getOrElse SMTParser2InputAbsy.SMTInteger)
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
    var oldTypedFormula : IFormula = null
    while (!(typedFormula eq oldTypedFormula)) {
      oldTypedFormula = typedFormula
      typedFormula =
        VariableTypeInferenceVisitor.visit(typedFormula, ())
                                    .asInstanceOf[IFormula]
    }
//    val bitvecFormula = (new BitVectorTranslator).visit(typedFormula, ())
    AbsyPrinter(typedFormula)
  }
  
  def printTerm(term : ITerm) =
    AbsyPrinter(term)
  
  def close {
    println("(check-sat)")
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  import SMTParser2InputAbsy.{SMTType, SMTArray, SMTBool, SMTInteger,
                              SMTFunctionType}

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

  private val type2Predicate = new MHashMap[SMTType, Predicate]
  private val predicate2Type = new MHashMap[Predicate, SMTType]

  private def getTypePredicate(t : SMTType) : Predicate =
    type2Predicate.getOrElseUpdate(t, {
      val p = new Predicate("type_" + t, 1)
      predicate2Type.put(p, t)
      p
    })

  object TypePredicate {
    def unapply(t : IExpression) : Option[(ITerm, SMTType)] = t match {
      case IAtom(p, Seq(v)) => for (s <- predicate2Type get p) yield (v, s)
      case _                => None
    }
  }

  object TypedTerm {
    def unapply(t : ITerm)
               (implicit variableType : Int => Option[SMTType])
              : Option[(ITerm, Option[SMTType])] =
      Some((t, getTermType(t)))
  }

  object TypedTermSeq {
    def unapplySeq(ts : Seq[ITerm])
                  (implicit variableType : Int => Option[SMTType])
                 : Option[Seq[(ITerm, Option[SMTType])]] =
      Some(for (t <- ts) yield (t, getTermType(t)))
  }

  private object VariableTypeInferenceVisitor
                 extends CollectingVisitor[Unit, IExpression] {

    private val variableTypes = new ArrayBuffer[SMTType]

    private def setVariableType(variableIndex : Int, t : SMTType) : Unit = {
      val pos = variableTypes.size - variableIndex - 1
      val oldType = variableTypes(pos)
      if (oldType != null && oldType != t)
        Console.err.println("Warning: type clash during inference: " +
                            oldType + " vs " + t)
      variableTypes(pos) = t
    }

    private def equalTypes(t1 : ITerm, t2 : ITerm) : Unit = (t1, t2) match {
      case (IVariable(ind1), IVariable(ind2)) =>
        (getVariableType(ind1), getVariableType(ind2)) match {
          case (Some(t), None) => setVariableType(ind2, t)
          case (None, Some(t)) => setVariableType(ind1, t)
          case _ => // nothing
        }
      case (IVariable(ind), t) =>
        for (s <- getTermType(t)) setVariableType(ind, s)
      case (t, IVariable(ind)) =>
        for (s <- getTermType(t)) setVariableType(ind, s)
      case _ =>
        // nothing
    }

    implicit val getVariableType : Int => Option[SMTType] = (ind:Int) => {
      val pos = variableTypes.size - ind - 1
      variableTypes(pos) match {
        case null => None
        case t => Some(t)
      }
    }

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = {
      t match {
        case _ : IQuantified | _ : IEpsilon =>
          variableTypes += null
        case TypePredicate(IVariable(ind), s) =>
          setVariableType(ind, s)
        case IExpression.Eq(IFunApp(SimpleArray.Select(),
                            TypedTermSeq((IVariable(ind), None), indexes @ _*)),
                            TypedTerm((_, Some(resT))))
          if (indexes forall { case (_, s) => s.isDefined }) =>
            setVariableType(ind,
              SMTArray(indexes.toList map {
                         case (_, Some(t)) => t
                         case _ => null // cannot happen
                       }, resT))
        case IExpression.Eq(TypedTerm((_, Some(resT))),
                            IFunApp(SimpleArray.Select(),
                            TypedTermSeq((IVariable(ind), None), indexes @ _*)))
          if (indexes forall { case (_, s) => s.isDefined }) =>
            setVariableType(ind,
              SMTArray(indexes.toList map {
                         case (_, Some(t)) => t
                         case _ => null // cannot happen
                       }, resT))
        case IExpression.Eq(s, t) =>
          equalTypes(s, t)
        case ITermITE(_, s, t) =>
          equalTypes(s, t)
        case t@IFunApp(_, args) =>
          for (argTypes <- getArgTypes(t)) {
            for ((IVariable(ind), s) <- args.iterator zip argTypes.iterator)
              setVariableType(ind, s)
          }
        case t@IAtom(_, args) =>
          for (argTypes <- getArgTypes(t)) {
            for ((IVariable(ind), s) <- args.iterator zip argTypes.iterator)
              setVariableType(ind, s)
          }
        case _ =>
          // nothing
      }

      KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[IExpression]) : IExpression = t match {
      case IQuantified(Quantifier.ALL,
                       IBinFormula(IBinJunctor.Or,
                                   INot(TypePredicate(IVariable(0), _)),
                                   _)) |
           IQuantified(Quantifier.EX,
                       IBinFormula(IBinJunctor.And,
                                   TypePredicate(IVariable(0), _),
                                   _)) |
           IEpsilon(IBinFormula(IBinJunctor.And,
                                TypePredicate(IVariable(0), _),
                                _)) => {
        Seqs removeLast variableTypes
        t update subres
      }
      case _ : IQuantified => {
        val f@IQuantified(q, subF) = t update subres
        import IExpression._
        val res = getVariableType(0) match {
          case Some(t) => q match {
            case Quantifier.ALL =>
              all(getTypePredicate(t)(v(0)) ==> subF)
            case Quantifier.EX =>
              ex(getTypePredicate(t)(v(0)) & subF)
          }
          case None => f
        }
        Seqs removeLast variableTypes
        res
      }
      case _ : IEpsilon => {
        val f@IEpsilon(subF) = t update subres
        import IExpression._
        val res = getVariableType(0) match {
          case Some(t) => eps(getTypePredicate(t)(v(0)) & subF)
          case None => f
        }
        Seqs removeLast variableTypes
        res
      }
      case _ => t update subres
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Translate arithmetic constraints back to bit-vectors.
   */

/*
  private class BitVectorTranslator
                extends CollectingVisitor[Unit, IExpression] {

    import SMTParser2InputAbsy.SMTBitVec
    import IExpression._

    private val variableTypes = new ArrayBuffer[SMTType]

    private def setVariableType(variableIndex : Int, t : SMTType) : Unit =
      variableTypes(variableTypes.size - variableIndex - 1) = t

    implicit val getVariableType : Int => Option[SMTType] = (ind:Int) =>
      variableTypes(variableTypes.size - ind - 1) match {
        case null => None
        case t => Some(t)
      }

    private object BitWidthInferrer
                   extends CollectingVisitor[Unit, Option[Int]] {
      override def preVisit(t : IExpression,
                            arg : Unit) : PreVisitResult = t match {
        case _ : IVariable | _ : IConstant | _ : IFunApp =>
          ShortCutResult(
            for (SMTBitVec(width) <- getTermType(t.asInstanceOf[ITerm]))
            yield (width + 1))
        case IIntLit(value) =>
          ShortCutResult(Some(value.abs.getHighestSetBit + 1))
        case _ =>
          KeepArg
      }
      def postVisit(t : IExpression,
                    arg : Unit,
                    subres : Seq[Option[Int]]) : Option[Int] = t match {
        case t : IPlus =>
          for (left <- subres(0); right <- subres(1))
          yield ((left max right) + 1)
        case ITimes(coeff, _) =>
          for (bits <- subres(0))
          yield (bits + coeff.abs.getHighestSetBit)
        case _ =>
          None
      }
    }

    private object BitVectorPadder
                   extends CollectingVisitor[Int, ITerm] {
      override def preVisit(t : IExpression,
                            newWidth : Int) : PreVisitResult = t match {
        case _ : IVariable | _ : IConstant | _ : IFunApp => {
          val Some(SMTBitVec(oldWidth)) = getTermType(t.asInstanceOf[ITerm])
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(SMTLineariser.AC, oldWidth < newWidth)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          ShortCutResult(getZeroExtend(newWidth - oldWidth)
                                      (t.asInstanceOf[ITerm]))
        }
        case t : IIntLit =>
          ShortCutResult(
            ModuloArithmetic.cast2UnsignedBV(newWidth, t))
        case _ =>
          KeepArg
      }
      def postVisit(t : IExpression,
                    newWidth : Int,
                    subres : Seq[ITerm]) : ITerm = t match {
        case _ : IPlus =>
          bvadd(subres(0), subres(1))
        case ITimes(IdealInt.MINUS_ONE, _) =>
          bvneg(subres(0))
        case ITimes(coeff, _) =>
          bvmul(ModuloArithmetic.cast2UnsignedBV(newWidth, coeff),
                subres(0))
      }
    }

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = {
      t match {
        case _ : IQuantified | _ : IEpsilon =>
          variableTypes += null
        case TypePredicate(IVariable(ind), s) =>
          setVariableType(ind, s)
        case _ =>
          // nothing
      }
      KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case _ : IQuantified | _ : IEpsilon => {
        Seqs removeLast variableTypes
        t update subres
      }
        
      case IIntFormula(rel, _) => subres(0) match {
        case Difference(TypedTerm(s, Some(SMTBitVec(sWidth))),
                        TypedTerm(t, Some(SMTBitVec(tWidth))))
          if (sWidth == tWidth) => rel match {
            case IIntRelation.GeqZero => bvuge(s, t)
            case IIntRelation.EqZero  => eqPredicate(s, t)
          }
        case IPlus(IIntLit(value),
                   TypedTerm(t, Some(SMTBitVec(width))))
          if (value.signum <= 0 && value > -(IdealInt(2) pow width)) =>
          rel match {
            case IIntRelation.GeqZero =>
              bvuge(t, ModuloArithmetic.cast2UnsignedBV(width, -value))
            case IIntRelation.EqZero =>
              eqPredicate(t, ModuloArithmetic.cast2UnsignedBV(width, -value))
          }
        case _ if prettyBitvectors =>
          BitWidthInferrer.visit(subres(0), ()) match {
            case Some(newWidth) => {
              val pred = rel match {
                case IIntRelation.GeqZero => bvsge
                case IIntRelation.EqZero => eqPredicate
              }
              pred(BitVectorPadder.visit(subres(0), newWidth),
                   ModuloArithmetic.cast2UnsignedBV(newWidth, 0))
            }
            case None =>
              t update subres
          }
        case _ =>
          t update subres
        }
      case _ =>
        t update subres
    }
  }
 */

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
      
      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO), IIntLit(upper),
                       IIntLit(value)))
          if prettyBitvectors && (upper & (upper + 1)).isZero => {
        print("(_ bv" + (value % (upper + 1)) + " " +
              (upper.getHighestSetBit + 1) + ")")
        shortCut(ctxt)
      }

      case IFunApp(ModuloArithmetic.bv_extract,
                   Seq(IIntLit(upper), IIntLit(lower), arg)) => {
        print("((_ extract " + upper + " " + lower + ") ")
        TryAgain(arg, ctxt addParentOp ")")
      }

      case StringTheory.ConcreteString(str) => {
        print("\"")
        print(escapeString(str))
        print("\"")
        shortCut(ctxt)
      }

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
          print(fun2Identifier(fun))
          shortCut(ctxt)
        } else {
          print("(" + fun2Identifier(fun) + " ")
          closeWithParen(ctxt, args.size)
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
      case IExpression.Eq(ADT.BoolADT.True, t) =>
        // strip off the ADT encoding
        TryAgain(t, ctxt)
      case IExpression.Eq(t, ADT.BoolADT.True) =>
        // strip off the ADT encoding
        TryAgain(t, ctxt)
      case IExpression.Eq(ADT.BoolADT.False, t) =>
        // strip off the ADT encoding
        TryAgain(!IExpression.eqZero(t), ctxt)
      case IExpression.Eq(t, ADT.BoolADT.False) =>
        // strip off the ADT encoding
        TryAgain(!IExpression.eqZero(t), ctxt)

      case IExpression.EqLit(BooleanTerm(t), v) =>
        // strip off the integer encoding
        if (v.isZero)
          TryAgain(t, ctxt)
        else
          TryAgain(!IExpression.eqZero(t), ctxt)

      // ADT expression
      case IExpression.EqLit(IFunApp(ADT.CtorId(adt, sortNum), Seq(arg)),
                             num) => {
        // insert a dummy predicate to represent the tester
        val testPred =
          new Predicate("is-" + adt.getCtorPerSort(sortNum,
                                                   num.intValueSafe).name, 1)
        TryAgain(new IAtom (testPred, List(arg)), ctxt)
      }

      // General equations
      case IExpression.Eq(s, t) =>
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

      case f@IQuantified(Quantifier.ALL, _) => {
        print("(forall (")

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
          case IQuantified(Quantifier.ALL,
                           IBinFormula(IBinJunctor.Or,
                                       INot(TypePredicate(IVariable(0), t)),
                                       g)) => {
            pushVar(t)
            curF = g
          }
          case IQuantified(Quantifier.ALL, g) => {
            pushVar(SMTInteger)
            curF = g
          }
          case _ => {
            cont = false
          }
        }

        print(") ")
        TryAgain(curF, curCtxt addParentOp ")")
      }

      case f@IQuantified(Quantifier.EX, _) => {
        print("(exists (")

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
          case IQuantified(Quantifier.EX,
                           IBinFormula(IBinJunctor.And,
                                       TypePredicate(IVariable(0), t),
                                       g)) => {
            pushVar(t)
            curF = g
          }
          case IQuantified(Quantifier.EX, g) => {
            pushVar(SMTInteger)
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
             ContainsSymbol.freeFrom(num1, Set(IVariable(0)))) => {
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
         if (ContainsSymbol.freeFrom(num, Set(IVariable(0), IVariable(1))) &&
             denom1 == denom2.abs) => {
        print("(mod ")
        visit(VariableShiftVisitor(num, 2, -2), ctxt)
        print(" " + toSMTExpr(denom2) + ")")
        shortCut(ctxt)
      }

      case IEpsilon(IBinFormula(IBinJunctor.And,
                                TypePredicate(IVariable(0), t),
                                subF)) => {
        val varName = "var" + ctxt.vars.size
        print("(_eps ((" + varName + " ")
        printSMTType(t)
        print(")) ")
        TryAgain(subF, ctxt.pushVar(varName, Some(t), ")" + ctxt.parentOp))
      }

      case _ : IEpsilon => {
        val varName = "var" + ctxt.vars.size
        print("(_eps ((" + varName + " ")
        printSMTType(SMTInteger)
        print(")) ")
        UniSubArgs(ctxt.pushVar(varName, None, ")"))
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

