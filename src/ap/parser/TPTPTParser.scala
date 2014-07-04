/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2014 Philipp Ruemmer <ph_r@gmx.net>
 *               2010-2012 NICTA/Peter Baumgartner <Peter.Baumgartner@nicta.com.au>
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

package ap.parser

import ap._
import ap.parameters.{ParserSettings, Param}
import ap.basetypes.{IdealInt, IdealRat}
import ap.terfor.Formula
import ap.util.Seqs

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}
import scala.util.parsing.combinator.{JavaTokenParsers, PackratParsers}
import scala.util.matching.Regex

object TPTPTParser {
  
  private type Env = Environment[Type, Type, Rank, Rank]
  
  def apply(settings : ParserSettings) =
    new TPTPTParser(new Env, settings)
  
  private case class TypedVar(name : String, t : Type)
  private type SyntaxError = Parser2InputAbsy.ParseException

  case class Type(name: String) {
    override def toString = name
  }
  
  // Types
  private object IType extends Type("$i") // Individuals (of the Herbrand Universe)
  // cannot call the object iType because if so Scala pattern matching assumes i
  // Type is a *variable*
  private object OType extends Type("$o") // Truth values
  private object TType extends Type("$tType") // The type of types (kinds)
  private object IntType extends Type("$int")
  private object RatType extends Type("$rat")
  private object RealType extends Type("$real")
  
  private val preDeclaredTypes = Set(TType, OType, IType, IntType, RatType, RealType)
  private val arithTypes = Set(IntType, RatType, RealType)
  private val interpretedTypes = arithTypes + OType

  // Notice: no space between - and digits
  private val isIntegerConstRegEx = """[+-]?[0-9]+""".r 
  
  // Predefined types: $i: individuals, $o: truth values
  // var types = Set(IType, OType, IntType, raTType, RealType)

  /**
   * Rank: The signature of individual function (and predicate) symbols.
   */

  case class Rank(rank: (List[Type], Type)) {
    def argsTypes = rank._1
    def resType = rank._2
    override def toString = 
      (if (argsTypes.isEmpty) "" else  ((argsTypes mkString " x ") + " -> ")) + resType
  }

  // Convenience functions

  private def Rank0(r: Type) = new Rank(List() -> r)
  private def Rank1(r: (Type, Type)) = new Rank(List(r._1) -> r._2)
  private def Rank2(r: ((Type, Type), Type)) = new Rank(List(r._1._1, r._1._2) -> r._2)
  private def Rank3(r: ((Type, Type, Type), Type)) = new Rank(List(r._1._1, r._1._2, r._1._2) -> r._2)

  private object TPTPType extends Enumeration {
    val FOF, TFF, CNF, Unknown = Value
  }
     
  private val singleQuotedQuote = """\\(['\\])""".r

}

/**
 * A parser for TPTP, both FOF and TFF
 */
class TPTPTParser(_env : Environment[TPTPTParser.Type,
                                     TPTPTParser.Type,
                                     TPTPTParser.Rank,
                                     TPTPTParser.Rank],
                  settings : ParserSettings)
      extends Parser2InputAbsy(_env)
      with JavaTokenParsers with PackratParsers {

  import IExpression._
  import TPTPTParser._
  import Parser2InputAbsy.warn
  
  private val booleanFunctionsAsPredicates =
    Param.BOOLEAN_FUNCTIONS_AS_PREDICATES(settings)
  private val triggersInConjecture =
    Param.TRIGGERS_IN_CONJECTURE(settings)
  private val partialQueries =    
    Param.MAKE_QUERIES_PARTIAL(settings)

  //////////////////////////////////////////////////////////////////////////////
    
  def apply(reader : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature) = {
    warn("You are using the normal version of Princess to solve TPTP problems.\n" +
         "         Note that this version assumes a non-standard semantics\n" +
         "         of uninterpreted sorts, defining all domains to be infinite.\n" +
         "         For full support of TPTP please download the dedicated\n" +
         "         CASC/TPTP of Princess from\n" +
         "         http://www.philipp.ruemmer.org/princess.shtml#tptp")

    parseAll[List[List[(Boolean, IFormula)]]](TPTP_input, reader) match {
      case Success(formulas, _) => {
        val axiomFors =
          (for (fors <- formulas.iterator;
                (false, f) <- fors.iterator) yield f).toList
        val conjectureFors =
          (for (fors <- formulas.iterator;
                (true, f) <- fors.iterator) yield f).toList

        val conjecture : IFormula =
          or(conjectureFors)
/*          if (conjectureFors.isEmpty)
            false
          else
            and(conjectureFors) */

//        println(formulas)

        val completeFor =
          (getAxioms &&& stringAxioms &&& genRRAxioms) ===>
            (or(axiomFors) ||| conjecture)

        (completeFor, List(), genSignature(completeFor))
      }
      case error =>
        throw new SyntaxError(error.toString)
    }
    
  }

  private var tptpType = TPTPType.Unknown

  //////////////////////////////////////////////////////////////////////////////
  
  private val declaredTypes = new MHashSet[Type]

  {
    declaredTypes ++= preDeclaredTypes
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private val occurringStrings =
    new scala.collection.mutable.HashMap[String, ConstantTerm]
    
  private def stringAxioms = {
    val stringConstants = occurringStrings.toSeq.sortWith(_._1 < _._1)
    connect(for (ind1 <- 0 until stringConstants.size;
                 ind2 <- (ind1+1) until stringConstants.size)
            yield (stringConstants(ind1)._2 =/= stringConstants(ind2)._2),
              IBinJunctor.And)
  }
  
  /**
   * Totality axioms?
   */
  private var totalityAxiom = true
  /**
   * Functionality axioms?
   */
  private var functionalityAxiom = true

  protected def defaultFunctionType(f : IFunction) : Rank = tptpType match {
    case TPTPType.FOF | TPTPType.CNF =>
      Rank(((for (_ <- 0 until f.arity) yield IType).toList, IType))
    case TPTPType.TFF =>
      Rank(((for (_ <- 0 until f.arity) yield IntType).toList, IntType))
  }

  private val arithmeticPreds = Set(
    "$less",
    "$lesseq",
    "$greater",
    "$greatereq",
    "$is_int",
    "$is_rat"
  )

  private val arithmeticOps = arithmeticPreds ++ Set(
    "$uminus",
    "$sum",
    "$difference",
    "$product",
    "$quotient",
    "$quotient_e",
    "$quotient_t",
    "$quotient_f",
    "$remainder_e",
    "$remainder_t",
    "$remainder_f",
    "$floor",
    "$ceiling",
    "$truncate",
    "$round",
    
    "$to_int",
    "$to_rat",
    "$to_real"
  )
  
  //////////////////////////////////////////////////////////////////////////////
  // Rationals
  
  private var containsRat = false
  
  private def foundRat = if (!containsRat) {
    containsRat = true
    
    if (tptpType == TPTPType.TFF) {
    warn("Problem contains rationals, using incomplete axiomatisation")
    
//    val oldPartial = totalityAxiom
//    totalityAxiom = false
    
    declareSym("rat_$less",        Rank2((RatType, RatType), OType))
    declareSym("rat_$lesseq",      Rank2((RatType, RatType), OType))
    declareSym("rat_$greater",     Rank2((RatType, RatType), OType))
    declareSym("rat_$greatereq",   Rank2((RatType, RatType), OType))
    declareSym("rat_$is_int",      Rank1((RatType), OType))
    declareSym("rat_$is_rat",      Rank1((RatType), OType))
    
    declareSym("rat_$uminus",      Rank1(RatType, RatType))
    declareSym("rat_$sum",         Rank2((RatType, RatType), RatType))
    declareSym("rat_$difference",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$product",     Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient",    Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_e",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_t",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_f",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_e", Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_t", Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_f", Rank2((RatType, RatType), RatType))
    declareSym("rat_$floor",       Rank1((RatType), RatType))
    declareSym("rat_$ceiling",     Rank1((RatType), RatType))
    declareSym("rat_$truncate",    Rank1((RatType), RatType))
    declareSym("rat_$round",       Rank1((RatType), RatType))
    
    declareSym("rat_$to_int",      Rank1((RatType), IntType))
    declareSym("rat_$to_rat",      Rank1((RatType), RatType))
    declareSym("rat_$to_real",     Rank1((RatType), RealType))
    
    declareSym("int_$to_rat",      Rank1((IntType), RatType))
    
    ratConstFor(IdealRat.ZERO)
    
//    totalityAxiom = oldPartial 
  }}
  
  //////////////////////////////////////////////////////////////////////////////
  // Reals
  
  private var containsReal = false
  
  private def foundReal = if (!containsReal) {
    containsReal = true
    
    if (tptpType == TPTPType.TFF) {
    warn("Problem contains reals, using incomplete axiomatisation")

//    val oldPartial = totalityAxiom
//    totalityAxiom = false

    declareSym("real_$less",        Rank2((RealType, RealType), OType))
    declareSym("real_$lesseq",      Rank2((RealType, RealType), OType))
    declareSym("real_$greater",     Rank2((RealType, RealType), OType))
    declareSym("real_$greatereq",   Rank2((RealType, RealType), OType))
    declareSym("real_$is_int",      Rank1((RealType), OType))
    declareSym("real_$is_rat",      Rank1((RealType), OType))
    
    declareSym("real_$uminus",      Rank1(RealType, RealType))
    declareSym("real_$sum",         Rank2((RealType, RealType), RealType))
    declareSym("real_$difference",  Rank2((RealType, RealType), RealType))
    declareSym("real_$product",     Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient",    Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_e",  Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_t",  Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_f",  Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_e", Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_t", Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_f", Rank2((RealType, RealType), RealType))
    declareSym("real_$floor",       Rank1((RealType), RealType))
    declareSym("real_$ceiling",     Rank1((RealType), RealType))
    declareSym("real_$truncate",    Rank1((RealType), RealType))
    declareSym("real_$round",       Rank1((RealType), RealType))
    
    declareSym("real_$to_int",      Rank1((RealType), IntType))
    declareSym("real_$to_rat",      Rank1((RealType), RatType))
    declareSym("real_$to_real",     Rank1((RealType), RealType))
    
    declareSym("int_$to_real",      Rank1((IntType), RealType))

    ratConstFor(IdealRat.ZERO)

//    totalityAxiom = oldPartial 
  }}

  //////////////////////////////////////////////////////////////////////////////
  
  private def genRRAxioms = {
    if (tptpType == TPTPType.TFF && (containsRat || containsReal))
      saturateRR

    val allLits = ratLiterals.toMap
    
    val res = tptpType match {
      case TPTPType.TFF => connect(
        // add full axioms
        (if (containsRat)
           generalRatAxioms("rat_", RatType, allLits mapValues (_._1)) ++
           (for ((value, (const, _)) <- allLits; if (value.denom.isOne))
            yield (checkUnintFunTerm("int_$to_rat", List(i(value.num)), List(IntType))._1 ===
                     const))
         else
           List()) ++
        (if (containsReal)
           generalRatAxioms("real_", RealType, allLits mapValues (_._2)) ++
           (for ((value, (_, const)) <- allLits; if (value.denom.isOne))
            yield (checkUnintFunTerm("int_$to_real", List(i(value.num)), List(IntType))._1 ===
                     const))
         else
           List())
        , IBinJunctor.And)
      case _ => connect(
        // only add information that numerals have distinct values
        (if (containsRat)
           distinctRatConstants(allLits.valuesIterator map (_._1))
         else
           List()) ++
        (if (containsReal)
           distinctRatConstants(allLits.valuesIterator map (_._2))
         else
           List())
        , IBinJunctor.And)
    }
    
//    println(res)
    res
  }
  
  private def saturateRR : Unit =
    for (_ <- 0 until Param.REAL_RAT_SATURATION_ROUNDS(settings)) {
      val allValues = ratLiterals.keys.toList
      for (val1 <- allValues.iterator; val2 <- allValues.iterator) {
        constsFor(-val1)

        constsFor(val1 + val2)
//        constsFor(-(val1 + val2))
        constsFor(val1 - val2)

        constsFor(val1 * val2)
//        constsFor(-(val1 * val2))

        if (!val1.isZero) {
          constsFor(IdealRat.ONE / val1)
//          constsFor(-(IdealRat.ONE / val1))
          constsFor(val2 / val1)
//          constsFor(-(val2 / val1))
        }
      }
    }

  private def distinctRatConstants(constants : Iterator[ConstantTerm]) = {
    val allConsts = (for (c <- constants) yield i(c)).toSeq
    for (i <- 0 until allConsts.size;
         j <- (i+1) until allConsts.size) yield (allConsts(i) =/= allConsts(j))
  }
  
  private def generalRatAxioms(prefix : String, t : Type,
                               constants : Map[IdealRat, ConstantTerm]) = {
    // instances of axioms for the defined literals
    
    implicit val _ = t
    
    val verySmall = new ConstantTerm(prefix + "very_small")
    val veryLarge = new ConstantTerm(prefix + "very_large")
    env.addConstant(verySmall,  Environment.NullaryFunction, t)
    env.addConstant(veryLarge,  Environment.NullaryFunction, t)

    val sortedValues = constants.keys.toList.sorted
    
    val boundedInstances = {
      //
      // binary predicates
      (for (predName <- Iterator("$less", "$lesseq", "$greater", "$greatereq");
            (value1, const1) <- constants.iterator;
            (value2, const2) <- constants.iterator;
            res <- evalRRPred(predName, value1, value2).iterator)
       yield rrPred(predName, !res, const1, const2)) ++
      //
      // literals are pairwise different
      {
        val allConsts =
          (List(i(verySmall), i(veryLarge)) ++ (for (c <- constants.values) yield i(c))).toSeq
        for (i <- (0 until allConsts.size).iterator;
             j <- ((i+1) until allConsts.size).iterator)
        yield (allConsts(i) =/= allConsts(j))
      }
    }.take(50000).toList

    boundedInstances ++
    //
    // unary predicates
    (for (predName <- List("$is_int", "$is_rat");
          (value, const) <- constants;
          res <- evalRRPred(predName, value).toSeq)
     yield rrPred(predName, !res, const)) ++
    //
    // unary functions
    (for (funName <- List("$uminus", "$floor", "$ceiling", "$truncate", "$round");
          (value, const) <- constants;
          res <- evalRRFun(funName, value).toSeq;
          resConst <- findRepresentations(res, t))
     yield (rrFun(funName, const) === resConst)) ++
    //
    // coercion function $to_int
    (for ((value, const) <- constants;
          res <- evalRRFun("$floor", value).toSeq)
     yield (rrFun("$to_int", const) === res.num)) ++
    //
    // coercion functions $to_rat, $to_real
    (for ((funName, resType) <- List(("$to_rat", RatType), ("$to_real", RealType));
          (value, const) <- constants;
          resConst <- findRepresentations(value, resType))
     yield (rrFun(funName, const) === resConst)) ++
    //
    // binary predicates
    (for (Seq(value1, value2) <- (sortedValues sliding 2).toSeq;
          const1 = constants(value1);
          const2 = constants(value2);
          res <- evalRRPred("$less", value1, value2).toSeq)
     yield rrPred("$less", !res, const1, const2)) ++
    //
    // binary functions
    (for (funName <- List("$sum", "$difference", "$product", "$quotient",
                          "$quotient_e", "$quotient_t", "$quotient_f",
                          "$remainder_e", "$remainder_t", "$remainder_f");
          (value1, const1) <- constants; (value2, const2) <- constants;
          res <- evalRRFun(funName, value1, value2).toSeq;
          resConst <- findRepresentations(res, t))
     yield (rrFun(funName, const1, const2) === resConst)) ++
    //
    // existence of very small/large elements
    (for ((_, const) <- constants)
     yield rrPred("$less", false, verySmall, const) &
           rrPred("$less", false, const, veryLarge) &
           rrPred("$greater", false, const, verySmall) &
           rrPred("$greater", false, veryLarge, const)) ++
    List(rrPred("$less", false, verySmall, veryLarge),
         rrPred("$lesseq", false, verySmall, veryLarge),
         rrPred("$greater", true, verySmall, veryLarge),
         rrPred("$greatereq", true, verySmall, veryLarge)) ++
    //
    // quantified axioms
    //
    List(//
         // binary relations
         //
         all(all(rrPred("$less", false, v(0), v(1)) <=>
                 rrPred("$greater", false, v(1), v(0)))),
         all(all(rrPred("$lesseq", false, v(0), v(1)) <=>
                 rrPred("$greatereq", false, v(1), v(0)))),
         all(all((rrPred("$less", false, v(0), v(1)) | (v(0) === v(1))) <=>
                 rrPred("$lesseq", false, v(0), v(1)))),
//         all(all(rrPred("$less", false, v(0), v(1)) ==> (v(0) =/= v(1)))),
         all(all(all((rrPred("$less", false, v(0), v(1)) &
                      rrPred("$lesseq", false, v(1), v(2))) ==>
                     rrPred("$less", false, v(0), v(2))))),
         all(all(all((rrPred("$lesseq", false, v(0), v(1)) &
                      rrPred("$less", false, v(1), v(2))) ==>
                     rrPred("$less", false, v(0), v(2))))),
         all(all(all((rrPred("$lesseq", false, v(0), v(1)) &
                      rrPred("$lesseq", false, v(1), v(2))) ==>
                     rrPred("$lesseq", false, v(0), v(2))))),
         //
         // R/Q with + forms an abelian group
         //
         all(all(rrFun("$sum", v(0), v(1)) === rrFun("$sum", v(1), v(0)))),
         all(all(all(rrFun("$sum", v(0), rrFun("$sum", v(1), v(2))) ===
                     rrFun("$sum", rrFun("$sum", v(0), v(1)), v(2))))),
         all(rrFun("$sum", v(0), constants(IdealRat.ZERO)) === v(0)),
         all(rrFun("$sum", v(0), rrFun("$uminus", v(0))) === constants(IdealRat.ZERO)),
         all(all(rrFun("$sum", v(0), rrFun("$uminus", v(1))) ===
                 rrFun("$difference", v(0), v(1)))),
         //
         // lemmas about negation
         //
         all((v(0) === rrFun("$uminus", v(0))) ==>
             (v(0) === constants(IdealRat.ZERO))),
         all(rrFun("$uminus", rrFun("$uminus", v(0))) === v(0)),
         //
         // lemmas about multiplication
         //
         all(all(rrFun("$product", v(0), v(1)) === rrFun("$product", v(1), v(0)))),
         all(all((v(1) === constants(IdealRat.ZERO)) |
                 (rrFun("$quotient", rrFun("$product", v(0), v(1)), v(1)) === v(0))))
         )
  }

  private def rrPred(op : String, negated : Boolean, args : ITerm*)
                    (implicit t : Type) : IFormula =
    checkUnintAtom((t match { case RatType => "rat_"; case RealType => "real_" }) + op,
                   args.toList, for (_ <- args.toList) yield t, negated)

  private def rrFun(op : String, args : ITerm*)(implicit t : Type) : ITerm =
    checkUnintFunTerm((t match { case RatType => "rat_"; case RealType => "real_" }) + op,
                      args.toList, for (_ <- args.toList) yield t)._1
  
  private def findRepresentations(r : IdealRat, t : Type) : Seq[ITerm] =
    (for ((c1, c2) <- (ratLiterals get r).toSeq)
     yield i(t match { case RatType => c1; case RealType => c2 })) /* ++
    (if (r.denom.isOne) List(CheckedFunTerm(t match { case RatType => "$to_rat"
                                                      case RealType => "$to_real" },
                                            List((r.num, IntType)))._1) else List()) */
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def evalRRPred(op : String,
                         left : IdealRat,
                         right : IdealRat) : Option[Boolean] = op match {
    case "$less"                         => Some(left < right)
    case "$lesseq"                       => Some(left <= right)
    case "$greater"                      => Some(left > right)
    case "$greatereq"                    => Some(left >= right)
    case _                               => None
  }
  
  private def evalRRPred(op : String,
                         arg : IdealRat) : Option[Boolean] = op match {
    case "$is_int"                       => Some(arg.denom.isOne)
    case "$is_rat"                       => Some(true)
    case _                               => None
  }
  
  private def evalRRFun(op : String,
                        left : IdealRat,
                        right : IdealRat) : Option[IdealRat] = op match {
    case "$sum"                          => Some(left + right)
    case "$difference"                   => Some(left - right)
    case "$product"                      => Some(left * right)
    case "$quotient" if (!right.isZero)  => Some(left / right)
    case _                               => None
  }
  
  private def evalRRFun(op : String, arg : IdealRat) : Option[IdealRat] = op match {
    case "$uminus"     => {
      Some(-arg)
    }
    case "$floor"     => {
      val res = IdealRat(arg.num / arg.denom)
      Some(if (res <= arg) res else (res - IdealRat.ONE))
    }
    case "$ceiling"   => {
      val res = IdealRat(arg.num / arg.denom)
      Some(if (res >= arg) res else (res + IdealRat.ONE))
    }
    case "$truncate"  => Some(arg.signum match {
      case -1 => -IdealRat((-arg.num) / arg.denom)
      case  0 => IdealRat.ZERO
      case  1 => IdealRat(arg.num / arg.denom)
    })
    case "$round"     => {
      for (f <- evalRRFun("$floor", arg);
           c <- evalRRFun("$ceiling", arg))
      yield (if ((f == c) || (arg - f) < (c - arg))
               f
             else
               c)
    }
    case _ => None
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val ratLiterals = new MHashMap[IdealRat, (ConstantTerm, ConstantTerm)]
  private val ratLitValue = new MHashMap[ConstantTerm, IdealRat]
  
  private def constsFor(r : IdealRat) = ratLiterals.getOrElseUpdate(r, {
    val ratConst = new ConstantTerm ("rat_" + r)
    val realConst = new ConstantTerm ("real_" + r)
    env.addConstant(ratConst,  Environment.NullaryFunction, RatType)
    env.addConstant(realConst, Environment.NullaryFunction, RealType)
    ratLitValue += (ratConst -> r)
    ratLitValue += (realConst -> r)
    (ratConst, realConst)
  })
  
  private def ratConstFor(r : IdealRat)  = constsFor(r)._1
  private def realConstFor(r : IdealRat) = constsFor(r)._2
  
  private object RRValue {
    def unapply(t : ITerm) : Option[IdealRat] = t match {
      case IConstant(c) => ratLitValue get c
      case _            => None
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Comments are considered as whitespace and ignored right away
   */
  protected override val whiteSpace = """(\s|%.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
  
  /**
   * The grammar rules
   */
  private lazy val TPTP_input: PackratParser[List[List[(Boolean, IFormula)]]] =
    rep(annotated_formula /* | comment */ | include)

  private lazy val annotated_formula = 
    // TPTP_input requires a list, because include abobe returns a list
    ( fof_annotated_logic_formula ^^ { List(_) } ) |
    ( cnf_annotated_logic_formula ^^ { List(_) } ) |
    ( tff_annotated_type_formula ^^ { _ => List() } ) |
    ( tff_annotated_logic_formula ^^ { List(_) } ) 
  // cnf_annotated


  private lazy val fof_annotated_logic_formula =
    ("fof" ^^ { _ => tptpType = TPTPType.FOF }) ~ "(" ~>
    (atomic_word | wholeNumber) ~ "," ~
    formula_role_other_than_type ~ "," ~ fof_logic_formula <~ ")" ~ "." ^^ {
    case name ~ "," ~ role ~ "," ~ f => 
	role match {
	  case "conjecture" =>
            (true, f)
          case _ =>
            (false, !f) // Assume f sits on the premise side
	}
  } 

  private lazy val cnf_annotated_logic_formula =
    ("cnf" ^^ { _ => tptpType = TPTPType.CNF }) ~ "(" ~>
    (atomic_word | wholeNumber) ~ "," ~
    formula_role_other_than_type ~ "," ~
    fof_logic_formula <~ ")" ~ "." ^^ {
    case name ~ "," ~ role ~ "," ~ f => 
    role match {
      case "conjecture" => {
        assert(false)
        null
      }
      case _ => { // Assume f sits on the premise side
        // we have to add quantifiers for all variables in the problem
        var res =
          if (env.declaredVariableNum > 0) possiblyEmptyTrigger(f) else f
        while (env.declaredVariableNum > 0) {
          res = all(res)
          env.popVar
        }
        (false, !res)
      }
    }
  } 

  /**
   * TFF types
   */

  // In fact, non-null annotations are currently not accepted
  // Slightly rewritten version of the BNF rule in the TPTP report, to discrimate
  // between type and non-type very early, thus helping the parser.
  private lazy val tff_annotated_type_formula =
    (("tff" ^^ { _ => tptpType = TPTPType.TFF }) ~ "(" ~
     (atomic_word | wholeNumber) ~ "," ~ "type" ~ "," ~> tff_typed_atom ~
       opt("," ~> formula_source ~ opt("," ~> formula_useful_info)) <~ ")" ~ ".") ^^ {
       case declarator ~ None           => declarator()
       case declarator ~ Some(_ ~ None) => declarator()

       case declarator ~ Some(_ ~ Some(infos)) => {
         val oldTotality = totalityAxiom
         val oldFunctionality = functionalityAxiom

         if (infos contains "partial")
           totalityAxiom = false
         if (infos contains "relational")
           functionalityAxiom = false

         val res = declarator()

         totalityAxiom = oldTotality
         functionalityAxiom = oldFunctionality

         res
       }
    }

  private lazy val formula_source : PackratParser[Unit] =
    ( "unknown" | "source_unknown" ) ^^ { case _ => () }

  private lazy val formula_useful_info : PackratParser[Seq[String]] =
    "[" ~> rep1sep(atomic_word, ",") <~ "]"

  private var inConjecture = false
  
  private def possiblyEmptyTrigger(f : IFormula) =
    if (inConjecture && !triggersInConjecture)
      // create an empty trigger, to prevent
      // the trigger heuristic from choosing
      // triggers
      ITrigger(List(), f)
    else
      f
      
  private lazy val tff_annotated_logic_formula =
    ("tff" ^^ { _ => tptpType = TPTPType.TFF }) ~ "(" ~
    (atomic_word | wholeNumber) ~ "," ~ 
    formula_role_other_than_type ~ "," ~ tff_logic_formula <~ ")" ~ "." ^^ {
      case name ~ "," ~ role ~ "," ~ f => 
	  role match {
            case "conjecture" =>
              (true, f)
            case _ =>
              (false, !f) // Assume f sits on the premise side
	  }
    } 

  private lazy val formula_role_other_than_type = commit(
    // "type" | 
    "axiom" | "hypothesis" | "definition" | "assumption" | "lemma" | "theorem" | 
    "conjecture" | "negated_conjecture" | "unknown" | atomic_word ) ^^ {
      case role@("conjecture" | "negated_conjecture") => {
        inConjecture = true
        role
      }
      case role => {
        inConjecture = false
        role
      }
    }


  // tff_typed_atom can appear only at toplevel
  private lazy val tff_typed_atom:PackratParser[() => Unit] =
     ( ( tff_untyped_atom ~ ":" ~ tff_top_level_type ) ^^ { 
	        // could declare a new type or a symbol of an existing type
       case typeName ~ ":" ~ Rank((Nil, TType)) => { () =>
         // TODO: we have to add guards to encode that uninterpreted domains
         // could be finite
	     declaredTypes += Type(typeName)
	     ()
	     //Sigma += Type(typeName)
         // println("declared")
         // return a dummy
         // TrueAtom
       }
       case symbolName ~ ":" ~ rank => { () =>
         declareSym(symbolName, rank)
       }
     } ) |
     ( "(" ~> tff_typed_atom <~ ")" )
           
         
  private def declareSym(symbolName : String, rank : Rank) : Unit = {
         if (rank.argsTypes contains OType)
           throw new SyntaxError("Error: type declaration for " + 
               symbolName + ": " + rank + ": argument type cannot be $oType")
         
         if (!rank.argsTypes.isEmpty) {
           if (!booleanFunctionsAsPredicates || rank.resType != OType) {
             // use a real function

             val partial =
               !totalityAxiom ||
               (partialQueries &&
                ((interpretedTypes contains rank.resType) ||
                 !(rank.argsTypes exists interpretedTypes)))

             env.addFunction(new IFunction(symbolName, rank.argsTypes.size,
                                           partial, !functionalityAxiom),
                             rank)
           } else {
             // use a predicate
             env.addPredicate(new Predicate(symbolName, rank.argsTypes.length),
                              rank)
           }
         } else if (rank.resType != OType)
           // use a constant
           env.addConstant(new ConstantTerm(symbolName), Environment.NullaryFunction,
                           rank.resType)
         else
           // use a nullary predicate (propositional variable)
           env.addPredicate(new Predicate(symbolName, 0), rank)
  }
     
  private lazy val tff_untyped_atom =    atomic_word

  // This results in a Rank in our terminology
  private lazy val tff_top_level_type:PackratParser[Rank] =
    tff_mapping_type |
    ( tff_atomic_type  ^^ { (typ:Type) => Rank0(TypeExistsChecked(typ)) } )

  private lazy val tff_mapping_type:PackratParser[Rank] =
    ( ( tff_unitary_type ~ ">" ~ tff_atomic_type ) ^^
        { case argsTypes ~ ">" ~ resType =>
          Rank((argsTypes map (TypeExistsChecked(_))) -> TypeExistsChecked(resType)) } ) | (
            "(" ~> tff_mapping_type <~ ")" )
    
  private lazy val tff_unitary_type =
    ( tff_atomic_type ^^ { List(_) } ) | ( "(" ~> tff_xprod_type <~ ")" )
    
  private lazy val tff_xprod_type:PackratParser[List[Type]] =
    ( tff_atomic_type ~ "*" ~  rep1sep(tff_atomic_type, "*") ^^ {
      case t1 ~ "*" ~ tail => t1::tail
     } ) |
    ( "(" ~> tff_xprod_type <~ ")" )

  //////////////////////////////////////////////////////////////////////////////
   
  /**
   * TFF formulas
   */

  private lazy val tff_logic_formula =
    tff_binary_formula | tff_unitary_formula
    
  private lazy val tff_binary_formula =
    tff_binary_nonassoc | tff_binary_assoc
    
  private lazy val tff_binary_nonassoc =
    tff_unitary_formula ~ binary_nonassoc_connective ~ tff_unitary_formula ^^ {
      case f1 ~ op ~ f2 => op(f1,f2)
    }
  
  private lazy val tff_binary_assoc =
    tff_or_formula | tff_and_formula
    
  private lazy val tff_or_formula =
    tff_unitary_formula ~ "|" ~ rep1sep(tff_unitary_formula, "|") ^^ {
      case f1 ~ "|" ~ tail => f1::tail reduceLeft { _ | _ }
    }
  
  private lazy val tff_and_formula =     
    tff_unitary_formula ~ "&" ~ rep1sep(tff_unitary_formula, "&") ^^ {
      case f1 ~ "&" ~ tail => {
        f1::tail reduceLeft { _ & _ }
      }
    }
  
  private lazy val tff_ite_f_formula =
    "$ite_f" ~ "(" ~> tff_logic_formula ~ "," ~
                      tff_logic_formula ~ "," ~ tff_logic_formula <~ ")" ^^ {
    case cond ~ _ ~ left ~ _ ~ right => IFormulaITE(cond, left, right)
  }

  private lazy val tff_let_formula :PackratParser[IFormula] =
    ((("$let_tf" ~ "(" ~> functor /* term */ ~ "=" ~ term ^^ {
       case lhs_name ~ _ ~ rhs => {
//         val (lhs_t, lhs_type) = lhs
         val (rhs_t, rhs_type) = rhs
//         if (!lhs_t.isInstanceOf[IConstant])
//           throw new SyntaxError(
//              "Error: currently $let_tf only supports constants, not " + lhs_t)
//         val IConstant(c) = lhs_t
//         if (lhs_type == OType || lhs_type != rhs_type) {
//           throw new SyntaxError(
//              "Error: ill-sorted $let_tf: between " + lhs_t + " and " + rhs_t + "." +
//              " Possibly the type of " + lhs_t + " has to be declared.")
//           warn("ill-sorted $let_tf: between " + lhs_t + " and " + rhs_t + ".")
//         }
         env.pushVar(lhs_name, rhs_type)
         rhs_t
       }
     }) ~ "," ~ tff_logic_formula <~ ")") ^^ {
      case rhs_t ~ _ ~ body => {
        env.popVar
        VariableSubstVisitor(body, (List(rhs_t), -1))
//        ConstantSubstVisitor(body, Map(definition))
      }
    }) |
    ("$let_ff" ~ "(" ~> tff_unitary_formula ~ "<=>" ~ tff_logic_formula ~
                       "," ~ tff_logic_formula <~ ")" ^^ {
      case lhs ~ _ ~ rhs ~ _ ~ body => {
        lhs match {
          case IAtom(p, Seq()) => // nothing
          case _ =>
            throw new SyntaxError(
               "Error: currently $let_ff only supports Boolean variables, not " + lhs)
        }
        val IAtom(p, _) = lhs
        PredicateSubstVisitor(body, Map(p -> rhs))
      }
    })

  private lazy val tff_unitary_formula:PackratParser[IFormula] = 
    tff_quantified_formula | tff_unary_formula |
    tff_ite_f_formula | tff_let_formula |
    (guard(not("$ite_f" | "$let_tf" | "$let_ff")) ~> atom) |
    "(" ~> tff_logic_formula <~ ")"
    
  private lazy val tff_unary_formula =
    "~" ~> tff_unitary_formula ^^ { ! _ }
  
  private lazy val tff_quantified_formula:PackratParser[IFormula] = 
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
	    ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
	     "[" ~ tff_varlist ~ "]" ^^ { 
		        case q ~ "[" ~ vl ~ "]" => { 
				  for (v <- vl)
				    env.pushVar(v.name, v.t)
				  // Return the partially instantiated Quantifier-Formula
				  val quantify = (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
				  (quantify, vl.size)
				}
		     }) ~ ":" ~ tff_unitary_formula ^^ {
		        // Put together the two parts, quantification and formula
		        case (quantTemplate, varNum) ~ ":" ~ f => {
                  for (_ <- 0 until varNum)
                    env.popVar
		          quantTemplate(possiblyEmptyTrigger(f))
		        }
		      }


  // Variable list
  private lazy val tff_varlist: PackratParser[List[TypedVar]] =
    rep1sep(tff_var, ",")

  private lazy val tff_var: PackratParser[TypedVar] = 
    ( variableStr ~ ":" ~ tff_atomic_type ^^ { 
        case x ~ ":" ~ typ => TypedVar(x, TypeExistsChecked(typ)) 
      } ) |
    ( variableStr <~ guard(not(":")) ^^ { 
        // default type of variables (in quantifications) is IType
        x => TypedVar(x, IType) 
      } )

  private lazy val tff_atomic_type = 
    // user-defined type
    defined_type | ( atomic_word ^^ { Type(_) } ) 
  // predefined type

  private lazy val defined_type: PackratParser[Type] = 
    (("$oType" | "$o") ^^ { _ => OType }) |
    (("$iType" | ("$i" <~ guard(not("nt")))) ^^ { _ => IType }) |
    ("$tType" ^^ { _ => TType }) |
    ("$int" ^^ { _ => IntType }) |
    ("$rat" ^^ { _ => foundRat; RatType }) |
    ("$real" ^^ { _ => foundReal; RealType })

  //////////////////////////////////////////////////////////////////////////////
    
  /*
   * FOF formulas
   */
  private lazy val fof_logic_formula =
    fof_binary_formula | fof_unitary_formula
    
  private lazy val fof_binary_formula =
    fof_binary_nonassoc | fof_binary_assoc
    
  private lazy val fof_binary_nonassoc =
    fof_unitary_formula ~ binary_nonassoc_connective ~ fof_unitary_formula ^^ {
      case f1 ~ op ~ f2 => op(f1,f2)
    }
  
  private lazy val fof_binary_assoc =
    fof_or_formula | fof_and_formula
    
  private lazy val fof_or_formula =
    fof_unitary_formula ~ "|" ~ rep1sep(fof_unitary_formula, "|") ^^ {
      case f1 ~ "|" ~ tail => f1::tail reduceLeft { _ | _ }
    }
  
  private lazy val fof_and_formula =     
    fof_unitary_formula ~ "&" ~ rep1sep(fof_unitary_formula, "&") ^^ {
      case f1 ~ "&" ~ tail => f1::tail reduceLeft { _ & _ }
    }
  
  private lazy val fof_unitary_formula:PackratParser[IFormula] = 
      fof_quantified_formula | fof_unary_formula | atom |
      "(" ~> fof_logic_formula <~ ")"
      
  private lazy val fof_unary_formula =
    "~" ~> fof_unitary_formula ^^ { !(_) }
  
  private lazy val fof_quantified_formula:PackratParser[IFormula] =
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
      ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
       "[" ~ fof_varlist ~ "]" ^^ { 
              case q ~ "[" ~ vl ~ "]" => { 
                for (v <- vl)
                  env.pushVar(v.name, v.t)
                // Return the partially instantiated Quantifier-Formula
                val quantify = (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
                (quantify, vl.size)
              } 
           }) ~ ":" ~ fof_unitary_formula ^^ {
              // Put together the two parts, quantification and formula
              case (quantTemplate, varNum) ~ ":" ~ f => {
                for (_ <- 0 until varNum)
                  env.popVar
                quantTemplate(possiblyEmptyTrigger(f))
              }
            }


  // Variable list
  private lazy val fof_varlist: PackratParser[List[TypedVar]] = 
    rep1sep(variableStr, ",") ^^ { _ map { TypedVar(_, IType) } } // looks cryptic?

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Definitions common to TFF and FOF
   */

  private lazy val binary_nonassoc_connective = 
    ( "=>" ^^ {
      _ => { (x : IFormula, y : IFormula) => (x ==> y) } } ) |
    ( "<=" <~ guard(not(">")) ^^ {
      _ => { (x : IFormula, y : IFormula) => (y ==> x) } } ) |
    ( "<=>" ^^ {
      _ => { (x : IFormula, y : IFormula) => (x <=> y) } } ) |
    ( "<~>" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x <=> y) } } ) |
    ( "~|" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x | y) } } ) |
    ( "~&" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x & y) } } )

  // Atom
  // Difficulty is determining the type. If fun(args...) has been read 
  // it is possible that fun(args...) is an atom or the lhs of an equation.
  // Determining the type hence nees to be deferred until "=" (or "!=") is 
  // seen (or not). Once that is clear, the signature is extended 
  // appropriately. It can only be done this late because otherwise the signature
  // might be extended unappropriately, and backtracking (in the parser)
  // cannot undo that.

  private lazy val atom : PackratParser[IFormula] =
    ( "$true" ^^ { _ => i(true) }) |
    ( "$false" ^^ { _ => i(false) }) |
    // eqn with lhs a variable
    ( guard(variableStr ~ equalsSign) ~> (constant_or_variable ~ equalsSign ~ term) ^^ { 
	      case x ~ _ ~ t => CheckedEquation(x, t)
      } ) |
    ( guard(variableStr ~ "!=") ~> (constant_or_variable ~ "!=" ~ term) ^^ { 
	      case x ~ _ ~ t => !CheckedEquation(x, t)
      } ) |
    ( bg_constant ~ equalsSign ~ term ^^ { 
	      case c ~ _ ~ t => CheckedEquation(c, t)
      } ) |
    ( bg_constant ~ "!=" ~ term ^^ { 
	  case c ~ _ ~ t => !CheckedEquation(c, t)
      } ) |
    ( "$distinct" ~ "(" ~> termlist <~ ")" ^^ {
      case termlist =>
        connect(for (ind1 <- 0 until termlist.size;
                     ind2 <- (ind1+1) until termlist.size)
                yield !CheckedEquation(termlist(ind1), termlist(ind2)),
                IBinJunctor.And)
      } ) |
  // $ite_t terms
    ( (tff_ite_t_term | tff_let_term) ~ ( equalsSign | "!=" ) ~ term ^^ {
        case lhs ~ "=" ~ rhs => CheckedEquation(lhs, rhs)
        case lhs ~ "!=" ~ rhs => !CheckedEquation(lhs, rhs)
      }) |
  // functor with or without arguments
  ( guard(not("$ite_t" | "$let_tt" | "$let_ft")) ~>
     ( ( functor ~ "(" ~ termlist ~ ")" ^^ { 
   	       case functor ~ "(" ~ termlist ~ ")" => (functor, termlist) } ) |
       ( functor ~ guard(not("(")) ^^ { 
	       case functor ~ _ => (functor, List()) } ) ) ~
   // Up to here the above could be an atom or the lhs of an equation.
   // The following three cases all return a template for a (dis)equation or an atom
   ( ( equalsSign ~ term ^^ { case _ ~ t =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//             Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       CheckedEquation(CheckedFunTerm(functor, args), t)
	     } 
       } ) |
     ( "!=" ~ term ^^ { 
         case _ ~ t =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//	         Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       !CheckedEquation(CheckedFunTerm(functor, args), t)
	     } 
       } ) |
     ( guard(not(equalsSign | "!=")) ^^ { 
         case _ =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//             Sigma += (functor -> Rank((args map { _ => IType }) -> OType))
	       CheckedAtom(functor, args)
	     } 
       } ) ) ^^ 
   // Put together the results of the parsing obtained so far
   { case (functor,args) ~ fTemplate => fTemplate(functor,args) } )

  // Terms
  // Parsing (of atoms) is such that whenever a term is to be parsed
  // it is clear it must be a term (no backtracking), hence as soon
  // as a term is found the signature can be extended.
  private lazy val term: PackratParser[(ITerm, Type)] =
    tff_ite_t_term | tff_let_term |
    (guard(not("$ite_t" | "$let_tf" | "$let_ff")) ~> (
       funterm | constant_or_variable | bg_constant))

  private lazy val variableStr: PackratParser[String] =
    regex(new Regex("[A-Z][a-zA-Z0-9_]*"))
    
/*    lazy val variable : PackratParser[] =
    variableStr ^^ { name => {
      val t = env.loo
    }} } */
    
  private lazy val funterm: PackratParser[(ITerm, Type)] =
    functor ~ "(" ~ termlist ~ ")" ^^ {
      case functor ~ "(" ~ termlist ~ ")" => CheckedFunTerm(functor, termlist)
        
//	      if (!(Sigma.ranks contains functor))
//	        Sigma += (functor -> Rank((termlist map { _ => IType }) -> IType))
	    // todo: check well-sortedness of arguments
//	    CheckedFunTerm(functor, termlist) 
  }

  private lazy val termlist = rep1sep(term, ",")

  // Foreground constant or parameter
  private lazy val constant_or_variable: PackratParser[(ITerm, Type)] = 
    // a constant cannot be followed by a parenthesis, would see a FunTerm instead
    // Use atomic_word instead of functor?
    guard((functor | variableStr) ~ not("(")) ~> (
      (functor ^^ { functor => {
        if (!(env isDeclaredSym functor)) {
          tptpType match {
            case TPTPType.TFF =>
              warn("implicit declaration of " + functor + ": " + IType)
            case _ =>
              // nothing
          }
          declareSym(functor, Rank0(IType))
        }
          
        (env lookupSym functor) match {
          case Environment.Constant(c, _, t) => (i(c), t)
          case Environment.Variable(ind, t) => (v(ind), t)
          case _ => throw new SyntaxError("Unexpected symbol: " + functor)
        }
        
      }}) | (
          
       variableStr ^^ { varStr => {
        if (!(env isDeclaredSym varStr)) {
          tptpType match {
            case TPTPType.TFF =>
              throw new SyntaxError("implicit declaration of " + varStr)
            case _ =>
              // nothing
          }
          env.pushVar(varStr, IType)
        }
         
       (env lookupSym varStr) match {
         case Environment.Variable(index, t)
           if (tptpType == TPTPType.CNF) =>
             (v(env.declaredVariableNum - index - 1), t)
         case Environment.Variable(index, t) =>
           (v(index), t)
         case _ =>
           throw new SyntaxError("Unexpected symbol: " + varStr)
       }
       }}
      )
    )


  //////////////////////////////////////////////////////////////////////////////
  // Terms specific to TFF

  private lazy val tff_ite_t_term =
    "$ite_t" ~ "(" ~> tff_logic_formula ~ "," ~
                      term ~ "," ~ term <~ ")" ^^ {
    case cond ~ _ ~ l ~ _ ~ r => {
      val (left, leftT) = l
      val (right, rightT) = r
      if (leftT != OType && leftT == rightT)
        (ITermITE(cond, left, right), leftT)
      else
        throw new SyntaxError(
           "Error: ill-sorted $ite_t: between " + left + " and " + right)
    }
  }

  private lazy val tff_let_term =
    ((("$let_tt" ~ "(" ~> functor /* term */ ~ "=" ~ term ^^ {
       case lhs_name ~ _ ~ rhs => {
//         val (lhs_t, lhs_type) = lhs
         val (rhs_t, rhs_type) = rhs
//         if (!lhs_t.isInstanceOf[IConstant])
//           throw new SyntaxError(
//              "Error: currently $let_tt only supports constants, not " + lhs_t)
//         val IConstant(c) = lhs_t
//         if (lhs_type == OType || lhs_type != rhs_type) {
//           throw new SyntaxError(
//              "Error: ill-sorted $let_tt: between " + lhs_t + " and " + rhs_t + "." +
//              " Possibly the type of " + lhs_t + " has to be declared.")
//           warn("ill-sorted $let_tt: between " + lhs_t + " and " + rhs_t + ".")
//         }
         env.pushVar(lhs_name, rhs_type)
         rhs_t
       }
     }) ~ "," ~ term <~ ")") ^^ {
      case rhs_t ~ _ ~ body => {
        env.popVar
        (VariableSubstVisitor(body._1, (List(rhs_t), -1)), body._2)
//        (ConstantSubstVisitor(body._1, Map(definition)), body._2)
      }
    }) |
    ("$let_ft" ~ "(" ~> tff_unitary_formula ~ "<=>" ~ tff_logic_formula ~
                       "," ~ term <~ ")" ^^ {
      case lhs ~ _ ~ rhs ~ _ ~ body => {
        lhs match {
          case IAtom(p, Seq()) => // nothing
          case _ =>
            throw new SyntaxError(
               "Error: currently $let_ff only supports Boolean variables, not " + lhs)
        }
        val IAtom(p, _) = lhs
        (PredicateSubstVisitor(body._1, Map(p -> rhs)), body._2)
      }
    })

  //////////////////////////////////////////////////////////////////////////////

  private def fofify(t : Type) = tptpType match {
    case TPTPType.FOF | TPTPType.CNF => IType
    case _ => t
  }
      
  // Background literal constant
  private lazy val bg_constant: PackratParser[(ITerm, Type)] =
    (
      (regex(isIntegerConstRegEx) <~ guard(not(regex("[./]".r)))) ^^ { 
	    s => (i(IdealInt(s)), fofify(IntType))
      }
    ) | (
      (regex(isIntegerConstRegEx) ~ "/" ~ regex(isIntegerConstRegEx)) ^^ {
        case num ~ _ ~ denom => {
          foundRat
          (i(ratConstFor(IdealRat(num + "/" + denom))), fofify(RatType))
        }
      }
    ) | (
      (regex(isIntegerConstRegEx) ~ "." ~ regex("""[0-9Ee\-]+""".r)) ^^ {
        case int ~ _ ~ frac => {
          foundReal
          (i(realConstFor(IdealRat(int + "." + frac))), fofify(RealType))
        }
      }
    ) | (
      regex(("\"([\\040-\\041\\043-\\0133\\0135-\\0176]|\\\\\"|\\\\\\\\)*\"").r) ^^ {
        case s =>
          (i(occurringStrings.getOrElseUpdate(s, {
             val c = new ConstantTerm ("stringConstant" + occurringStrings.size)
             env.addConstant(c, Environment.NullaryFunction, IType)
             c
           })), IType)
      }
    )
  
  // lexical: don't confuse = with => (the lexer is greedy)
  private lazy val equalsSign = "=" <~ guard(not(">"))
  
  private lazy val forallSign = "!" <~ guard(not("="))

  private lazy val functor = keyword | atomic_word

  private lazy val atomic_word: PackratParser[String] = 
    ( regex("""'([^'\\]|(\\['\\]))*'""".r) ^^ {
        x => singleQuotedQuote.replaceAllIn(x.drop(1).dropRight(1),
                                            m => m group 0) } ) |
    regex("[a-z][a-zA-Z0-9_]*".r)

  private lazy val keyword = regex("[$][a-z_]+".r)

/* Could be specific (but why?)
  lazy val keyword = 
    "$uminus"     |
    "$sum"        |
    "$difference" |
    "$product"    |
    ("$less" <~ guard(not("eq")))   |
    "$lesseq"     |
    ("$greater" <~ guard(not("eq")))  |
    "$greatereq"  |
    "$evaleq"     
*/

  // Parsing of comments is not optimal as they may not appear
  // inside formulas - essentially they are an atom
//  private lazy val comment: PackratParser[List[IFormula]] =
//    """%.*""".r ^^ (x => List(null /* Comment(x) */))

  private lazy val include: PackratParser[List[(Boolean, IFormula)]] = 
    "include" ~> "(" ~> atomic_word <~ ")" <~ "." ^^ { case fileName  => {
	    val TPTPHome = System.getenv("TPTP")
	    val filename = (if (TPTPHome == null) "" else TPTPHome + "/") + fileName
	    val reader = new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (filename)))
        parseAll[List[List[(Boolean, IFormula)]]](TPTP_input, reader) match {
          case Success(formulas, _) =>
            formulas.flatten
          case error =>
            throw new SyntaxError("When reading " + filename + "\n" + error)
	    }
	  } 
  }

  /**
   * CheckedXX: creates an XX, type-checked against sig and varTypes
   */
  private def CheckedEquation(s: (ITerm, Type), t: (ITerm, Type)) = {
    val (s_term, s_type) = s
    val (t_term, t_type) = t
    if (s_type != OType && s_type == t_type) 
      s_term === t_term
    else
      throw new SyntaxError(
         "Error: ill-sorted (dis)equation: between " + s_term + " and " + t_term)
  }

  private def CheckedAtom(pred: String,
                          args: List[(ITerm, Type)])
                         : IFormula = (pred, args map (_._2)) match {
    case ("$less",      Seq(IntType, IntType)) => args(0)._1 < args(1)._1
    case ("$lesseq",    Seq(IntType, IntType)) => args(0)._1 <= args(1)._1
    case ("$greater",   Seq(IntType, IntType)) => args(0)._1 > args(1)._1
    case ("$greatereq", Seq(IntType, IntType)) => args(0)._1 >= args(1)._1
    case ("$evaleq",    Seq(IntType, IntType)) => args(0)._1 === args(1)._1
    case ("$is_int",    Seq(IntType))          => true
    case ("$is_rat",    Seq(IntType))          => true
    case ("$is_real",   Seq(IntType))          => true
    case ("$is_rat",    Seq(RatType))          => true
    case ("$is_real",   Seq(RatType))          => true
    case ("$is_real",   Seq(RealType))         => true

    case (pred, argTypes)
      if ((arithmeticOps contains pred) && !Seqs.disjointSeq(arithTypes, argTypes)) =>
        argTypes match {
          case Seq(RatType, _*) =>
            checkUnintAtom("rat_" + pred, args map (_._1), argTypes)
          case Seq(RealType, _*) =>
            checkUnintAtom("real_" + pred, args map (_._1), argTypes)
          case _ =>
            // should not happen
            throw new SyntaxError("Operator " + pred +
                                  " cannot be applied to " +
                                  (argTypes mkString " x "))
      }

    case (pred, argTypes) =>
      checkUnintAtom(pred, args map (_._1), argTypes)
  }
  
  private def checkUnintAtom(pred: String,
                             args: Seq[ITerm], argTypes : Seq[Type],
                             negated : Boolean = false)
              : IFormula = {
        if (!(env isDeclaredSym pred)) {
          val rank = Rank((argTypes.toList, OType))
          if (tptpType == TPTPType.TFF || (pred endsWith "'"))
            warn("implicit declaration or overloading of " + pred + ": " + rank)
          declareSym(pred, rank)
        }

      (env lookupSym pred) match {
        case Environment.Function(f, r) if (r.resType == OType) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintAtom(pred + "'", args, argTypes, negated)
          } else {
            // then a predicate has been encoded as a function
            if (negated)
              IIntFormula(IIntRelation.EqZero, IPlus(IFunApp(f, args), -1))
            else
              IIntFormula(IIntRelation.EqZero, IFunApp(f, args))
          }
        case Environment.Predicate(p, _, r) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintAtom(pred + "'", args, argTypes, negated)
          } else {
            if (negated)
              !IAtom(p, args)
            else
              IAtom(p, args)
          }
        case _ =>
          throw new SyntaxError("Unexpected symbol: " + pred)
      }
  }
  
/*      // Assume that pred has been entered into sig already
    if (Sigma(pred).argsTypes == Sigma.typesOf(args, varTypes))
  Atom(pred, args)
    else
	throw new SyntaxError("Error: ill-sorted atom: " + Atom(pred, args)) */

  private def CheckedFunTerm(fun: String,
                             args: List[(ITerm, Type)])
                            : (ITerm, Type) = (fun, args map (_._2)) match {
    case ("$sum",         Seq(IntType, IntType))  => (args(0)._1 + args(1)._1, IntType)
    case ("$difference",  Seq(IntType, IntType))  => (args(0)._1 - args(1)._1, IntType)
    case ("$product",     Seq(IntType, IntType))  => (mult(args(0)._1, args(1)._1), IntType)
    case ("$uminus",      Seq(IntType))           => (-args(0)._1, IntType)
    case ("$quotient_e",  Seq(IntType, IntType))  => {
      // Euclidian division
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      (eps((mult(v(0), denom) <= num) &
           ((num < mult(v(0), denom) + denom) | (num < mult(v(0), denom) - denom))),
       IntType)
    }
    case ("$remainder_e",  Seq(IntType, IntType))  => {
      // Euclidian remainder
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      (eps((v(0) >= 0) & ((v(0) < denom) | (v(0) < -denom)) &
           ex(VariableShiftVisitor(num, 0, 1) ===
              mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1))),
       IntType)
    }

    case ("$quotient_t",  Seq(IntType, IntType))  => {
      // Truncation division
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      val rem = num - mult(v(0), denom)
      (eps(((rem < denom) | (rem < -denom)) & ((-rem < denom) | (-rem < -denom)) &
           ((rem > 0) ==> (num > 0)) & ((rem < 0) ==> (num < 0))),
       IntType)
    }
    case ("$remainder_t",  Seq(IntType, IntType))  => {
      // Truncation division
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      (eps(((v(0) < denom) | (v(0) < -denom)) & ((-v(0) < denom) | (-v(0) < -denom)) &
           ((v(0) > 0) ==> (num > 0)) & ((v(0) < 0) ==> (num < 0)) &
           ex(VariableShiftVisitor(num, 0, 1) ===
              mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1))),
       IntType)
    }

    case ("$quotient_f",  Seq(IntType, IntType))  => {
      // Floor division
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      val rem = num - mult(v(0), denom)
      (eps(((rem < denom) | (rem < -denom)) & ((-rem < denom) | (-rem < -denom)) &
           ((rem > 0) ==> (denom > 0)) & ((rem < 0) ==> (denom < 0))),
       IntType)
    }
    case ("$remainder_f",  Seq(IntType, IntType))  => {
      // Floor division
      val Seq(num, denom) = for ((a, _) <- args) yield VariableShiftVisitor(a, 0, 1)
      (eps(((v(0) < denom) | (v(0) < -denom)) & ((-v(0) < denom) | (-v(0) < -denom)) &
           ((v(0) > 0) ==> (denom > 0)) & ((v(0) < 0) ==> (denom < 0)) &
           ex(VariableShiftVisitor(num, 0, 1) ===
              mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1))),
       IntType)
    }

    case ("$to_int",      Seq(IntType))           => args(0)
    case ("$to_rat",      Seq(RatType))           => args(0)
    case ("$to_real",     Seq(RealType))          => args(0)

    case ("$to_rat",      Seq(IntType))           => {
      foundRat
      args(0)._1 match {
        case Const(value) =>
          (ratConstFor(IdealRat(value)), RatType)
        case _ =>
         checkUnintFunTerm("int_" + fun, args map (_._1), Seq(IntType))
      }
    }
    case ("$to_rat",      Seq(RealType))          => {
      foundRat
      args(0)._1 match {
        case RRValue(value) =>
          (ratConstFor(value), RatType)
        case _ =>
         checkUnintFunTerm("real_" + fun, args map (_._1), Seq(RealType))
      }
    }
    case ("$to_real",     Seq(IntType))           => {
      foundReal
      args(0)._1 match {
        case Const(value) =>
          (realConstFor(IdealRat(value)), RealType)
        case _ =>
         checkUnintFunTerm("int_" + fun, args map (_._1), Seq(IntType))
      }
    }
    case ("$to_real",     Seq(RatType))           => {
      foundReal
      args(0)._1 match {
        case RRValue(value) =>
          (realConstFor(value), RealType)
        case _ =>
         checkUnintFunTerm("rat_" + fun, args map (_._1), Seq(RatType))
      }
    }

    case (fun, argTypes)
      if ((arithmeticOps contains fun) && !Seqs.disjointSeq(arithTypes, argTypes)) =>
        args match {
        case Seq((RRValue(argValue), RatType))
          if (!(arithmeticPreds contains fun)) => 
          (for (resValue <- evalRRFun(fun, argValue))
           yield (i(ratConstFor(resValue)), RatType)) getOrElse (
             checkUnintFunTerm("rat_" + fun, args map (_._1), argTypes))
        case Seq((RRValue(argValue), RealType))
          if (!(arithmeticPreds contains fun)) => 
          (for (resValue <- evalRRFun(fun, argValue))
           yield (i(realConstFor(resValue)), RealType)) getOrElse (
             checkUnintFunTerm("real_" + fun, args map (_._1), argTypes))
        
        case Seq((RRValue(argValue1), RatType), (RRValue(argValue2), RatType))
          if (!(arithmeticPreds contains fun)) => 
          (for (resValue <- evalRRFun(fun, argValue1, argValue2))
           yield (i(ratConstFor(resValue)), RatType)) getOrElse (
             checkUnintFunTerm("rat_" + fun, args map (_._1), argTypes))
        case Seq((RRValue(argValue1), RealType), (RRValue(argValue2), RealType))
          if (!(arithmeticPreds contains fun)) => 
          (for (resValue <- evalRRFun(fun, argValue1, argValue2))
           yield (i(realConstFor(resValue)), RealType)) getOrElse (
             checkUnintFunTerm("real_" + fun, args map (_._1), argTypes))
        
        case Seq((_, RatType)) | Seq((_, RatType), (_, RatType)) =>
          checkUnintFunTerm("rat_" + fun, args map (_._1), argTypes)
        case Seq((_, RealType)) | Seq((_, RealType), (_, RealType)) =>
          checkUnintFunTerm("real_" + fun, args map (_._1), argTypes)
          
        case _ =>
          // should not happen
          throw new SyntaxError("Unexpected operator: " + fun)
      }

    case (fun, argTypes) =>
      checkUnintFunTerm(fun, args map (_._1), argTypes)
  }

  private def checkUnintFunTerm(fun: String, args: Seq[ITerm], argTypes : Seq[Type])
                               : (ITerm, Type) = {
        if (!(env isDeclaredSym fun)) {
          val rank = Rank((argTypes.toList, IType))
          if (tptpType == TPTPType.TFF || (fun endsWith "'"))
            warn("implicit declaration or overloading of " + fun + ": " + rank)
          declareSym(fun, rank)
        }
        
      (env lookupSym fun) match {
        case Environment.Function(f, r) if (r.resType != OType) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintFunTerm(fun + "'", args, argTypes)
          } else {
            (IFunApp(f, args), r.resType)
          }
        case Environment.Constant(c, _, t) => {
          if (!args.isEmpty)
            throw new SyntaxError("Constant does not accept arguments: " + functor)
          (IConstant(c), t)
        }
        case Environment.Variable(ind, t) => {
          if (!args.isEmpty)
            throw new SyntaxError("Variable does not accept arguments: " + functor)
          (IVariable(ind), t)
        }
        case _ =>
          throw new SyntaxError("Unexpected symbol: " + fun)
      }
  }
  
/*      
    // Assume that fun has been entered into sig already
    if (args.isEmpty) {
	// A constant. See if we have a foreground constant or parameter
	if (Sigma.BGRanks contains fun)
	  // We have a parameter
	  Param(fun)
	else
	  // Foreground Constant
        Const(fun) 
    } else if (Sigma(fun).argsTypes == Sigma.typesOf(args, varTypes)) 
	// Type Checking OK 
	FunTerm(fun, args)
    else
	throw new SyntaxError("Error: ill-sorted term: " + FunTerm(fun, args)) */

  private def TypeExistsChecked(typ: Type) = 
    if (declaredTypes contains typ)
      typ
    else
      throw new SyntaxError("Error: type has not been declared: " + typ)
}


