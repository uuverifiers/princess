/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2019 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

package ap.theories.bitvectors

import ap.theories._

import ap.Signature
import ap.parser._
import ap.parameters.{Param, ReducerSettings, GoalSettings}
import ap.terfor.{Term, VariableTerm, ConstantTerm, TermOrder, Formula,
                  ComputationLogger, TerForConvenience, OneTerm}
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               ReducerPluginFactory, IdentityReducerPlugin,
                               ReducerPlugin, NegatedConjunctions}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import LinearCombination.SingleTerm
import ap.terfor.substitutions.VariableShiftSubst
import ap.basetypes.IdealInt
import ap.types.{Sort, ProxySort, SortedIFunction, SortedPredicate}
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.util.{Debug, IdealRange, LRUCache, Seqs, Timeout}

import scala.collection.{Map => GMap}
import scala.collection.mutable.{ArrayBuffer, Map => MMap, HashSet => MHashSet,
                                 Set => MSet, ListBuffer, HashMap => MHashMap,
                                 LinkedHashMap}

/**
 * Theory for performing bounded modulo-arithmetic (arithmetic modulo some
 * number N). This in particular includes bit-vector/machine arithmetic.
 *
 * Class under construction ...
 */
object ModuloArithmetic extends Theory {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  val debug = false
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private val AC = Debug.AC_MODULO_ARITHMETIC

  override def toString = "ModuloArithmetic"

  val MultTheory = GroebnerMultiplication

  // TODO: move the following methods to IdealInt class, optimise

  private def pow2(bits : Int) : IdealInt =
    IdealInt(2) pow bits

  private def pow2(bits : IdealInt) : IdealInt =
    IdealInt(2) pow bits.intValueSafe

  private def pow2Mod(bits : IdealInt, modulus : IdealInt) : IdealInt =
    IdealInt(2).powMod(bits, modulus)

  private def pow2MinusOne(bits : Int) : IdealInt =
    pow2(bits) - IdealInt.ONE

  /**
   * Run-length encoding of a number, starting with the number of
   * least-significant zeroes.
   */
  private def runlengths(v : IdealInt) : Seq[Int] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, v.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val two = IdealInt(2)
    val res = new ArrayBuffer[Int]

    var curBit = IdealInt.ZERO
    var curNum = 0

    var rem = v

    while (!rem.isZero) {
      val (newRem, bit) = rem /% two
      if (bit == curBit) {
        curNum = curNum + 1
      } else {
        res += curNum
        curNum = 1
        curBit = bit
      }

      rem = newRem
    }

    res += curNum
    res
  }

  private def completedRunlengths(lens : Seq[Int],
                                  totalLen : Int) : Seq[Int] = {
    val lensSum = lens.sum
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, lensSum <= totalLen)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (lensSum < totalLen)
      lens ++ List(totalLen - lensSum)
    else
      lens
  }

  //////////////////////////////////////////////////////////////////////////////
  // API methods that infer the right bit-width based on types
  
  def bv(width : Int, num : IdealInt) : ITerm =
    cast2UnsignedBV(width, num)

  def concat(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_concat, List(extractBitWidth(t1), extractBitWidth(t2), t1, t2))
  def extract(begin : Int, end : Int, t : ITerm) : ITerm =
    IFunApp(bv_extract, List(begin, end, t))

  def bvnot(t : ITerm) : ITerm =
    IFunApp(bv_not, List(extractBitWidth(t), t))
  def bvneg(t : ITerm) : ITerm =
    IFunApp(bv_neg, List(extractBitWidth(t), t))
  def bvand(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_and, List(extractBitWidth(t1, t2), t1, t2))
  def bvor(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_or, List(extractBitWidth(t1, t2), t1, t2))
  def bvadd(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_add, List(extractBitWidth(t1, t2), t1, t2))
  def bvsub(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_sub, List(extractBitWidth(t1, t2), t1, t2))
  def bvmul(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_mul, List(extractBitWidth(t1, t2), t1, t2))
  def bvudiv(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_udiv, List(extractBitWidth(t1, t2), t1, t2))
  def bvsdiv(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_sdiv, List(extractBitWidth(t1, t2), t1, t2))
  def bvurem(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_urem, List(extractBitWidth(t1, t2), t1, t2))
  def bvsrem(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_srem, List(extractBitWidth(t1, t2), t1, t2))
  def bvsmod(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_smod, List(extractBitWidth(t1, t2), t1, t2))
  def bvshl(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_shl, List(extractBitWidth(t1, t2), t1, t2))
  def bvlshr(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_lshr, List(extractBitWidth(t1, t2), t1, t2))
  def bvashr(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_ashr, List(extractBitWidth(t1, t2), t1, t2))
  def bvxor(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_xor, List(extractBitWidth(t1, t2), t1, t2))
  def bvxnor(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_xnor, List(extractBitWidth(t1, t2), t1, t2))
  def bvcomp(t1 : ITerm, t2 : ITerm) : ITerm =
    IFunApp(bv_comp, List(extractBitWidth(t1, t2), t1, t2))

  def bvult(t1 : ITerm, t2 : ITerm) : IFormula =
    IAtom(bv_ult, List(extractBitWidth(t1, t2), t1, t2))
  def bvule(t1 : ITerm, t2 : ITerm) : IFormula =
    IAtom(bv_ule, List(extractBitWidth(t1, t2), t1, t2))
  def bvslt(t1 : ITerm, t2 : ITerm) : IFormula =
    IAtom(bv_slt, List(extractBitWidth(t1, t2), t1, t2))
  def bvsle(t1 : ITerm, t2 : ITerm) : IFormula =
    IAtom(bv_sle, List(extractBitWidth(t1, t2), t1, t2))

  def bvugt(t1 : ITerm, t2 : ITerm) : IFormula = bvult(t2, t1)
  def bvuge(t1 : ITerm, t2 : ITerm) : IFormula = bvule(t2, t1)
  def bvsgt(t1 : ITerm, t2 : ITerm) : IFormula = bvslt(t2, t1)
  def bvsge(t1 : ITerm, t2 : ITerm) : IFormula = bvsge(t2, t1)

  def zero_extend(addWidth : Int, t : ITerm) : ITerm =
    cast2UnsignedBV(extractBitWidth(t) + addWidth, t)
  def sign_extend(addWidth : Int, t : ITerm) : ITerm = {
    val w = extractBitWidth(t)
    cast2UnsignedBV(w + addWidth, cast2SignedBV(w, t))
  }

  private def extractBitWidth(t1 : ITerm, t2 : ITerm) : Int = {
    val width1 = extractBitWidth(t1)
    val width2 = extractBitWidth(t2)
    if (width1 != width2)
      throw new IllegalArgumentException(
        "method can only be applied to terms of the same bit-vector sort")
    width1
  }

  private def extractBitWidth(t : ITerm) : Int = (Sort sortOf t) match {
    case UnsignedBVSort(width) =>
      width
    case _ =>
      throw new IllegalArgumentException(
        "method can only be applied to terms with a bit-vector sort")
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Modulo sorts, representing the interval
   * <code>[lower, upper]</code> with wrap-around arithmetic.
   */
  case class ModSort(lower : IdealInt, upper : IdealInt)
             extends ProxySort(Sort.Interval(Some(lower), Some(upper))) {
    override val name : String = this match {
      case UnsignedBVSort(bits) =>
        "bv[" + bits + "]"
      case SignedBVSort(bits) =>
        "signed bv[" + bits + "]"
      case _ =>
        "mod[" + lower + ", " + upper + "]"
    }
    
    val modulus = upper - lower + IdealInt.ONE

    import IExpression._

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(mod_cast(lower, upper, d))
  }

  private def isPowerOf2(n : IdealInt) : Option[Int] =
    if (n.signum > 0 && (n & (n - 1)).isZero)
      Some(n.getHighestSetBit)
    else
      None

  /**
   * Object to create and recognise modulo sorts representing
   * unsigned bit-vectors.
   */
  object UnsignedBVSort {
    def apply(bits : Int) : ModSort =
      ModSort(IdealInt.ZERO, pow2MinusOne(bits))
    def unapply(s : Sort) : Option[Int] = s match {
      case ModSort(IdealInt.ZERO, upper) =>
        isPowerOf2(upper + 1)
      case _ =>
        None
    }
  }

  /**
   * Object to create and recognise modulo sorts representing
   * signed bit-vectors.
   */
  object SignedBVSort {
    def apply(bits : Int) : ModSort = {
      val upper = pow2(bits - 1)
      ModSort(-upper, upper - IdealInt.ONE)
    }
    def unapply(s : Sort) : Option[Int] = s match {
      case ModSort(lower, upper)
        if (lower.signum < 0 && upper + IdealInt.ONE == -lower &&
            (upper & (upper + 1)).isZero) =>
          if (upper.isZero)
            Some(1)
          else
            Some(upper.getHighestSetBit + 2)
      case _ =>
        None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Modulo and bit-vector operations.
   * See http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
   * for an explanation of the operations
   */

  private def getLowerUpper(arguments : Seq[Term]) : (IdealInt, IdealInt) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC,
      arguments(0).asInstanceOf[LinearCombination].isConstant &&
      arguments(1).asInstanceOf[LinearCombination].isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val lower = arguments(0).asInstanceOf[LinearCombination].constant
    val upper = arguments(1).asInstanceOf[LinearCombination].constant
    (lower, upper)
  }

  val _mod_cast = new SortedPredicate("mod_cast", 4) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      List(Sort.Integer, Sort.Integer, Sort.Integer, ModSort(lower, upper))
    }
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      val (lower, upper) = getLowerUpper(arguments)
      List(Sort.Integer, Sort.Integer, Sort.Integer, ModSort(lower, upper))
    }
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  /**
   * Function for mapping any number to an interval [lower, upper].
   * The function is applied as <code>mod_cast(lower, upper, number)</code>
   */
  val mod_cast = new SortedIFunction("mod_cast", 3, true, false) {
    private val argSorts =
      List(Sort.Integer, Sort.Integer, Sort.Integer)
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      (argSorts, ModSort(lower, upper))
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      val (lower, upper) = getLowerUpper(arguments)
      (argSorts, ModSort(lower, upper))
    }
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
    def toPredicate : SortedPredicate = _mod_cast
  }

  /**
   * Evaluate <code>mod_cast</code> with concrete arguments
   */
  def evalModCast(lower : IdealInt, upper : IdealInt,
                  number : IdealInt) : IdealInt =
    if (lower <= number && number <= upper) {
      number
    } else {
      val modulus = upper - lower + IdealInt.ONE
      val lowerFactor = (number - lower) / modulus
      number - (lowerFactor * modulus)
    }

  /**
   * Evaluate <code>bv_extract</code> with concrete arguments
   */
  def evalExtract(start : Int, end : Int, number : IdealInt) : IdealInt =
    (number % pow2(start+1)) / pow2(end)

  /**
   * Cast a term to a modulo sort.
   */
  def cast2Sort(sort : ModSort, t : ITerm) : ITerm =
    IFunApp(mod_cast, List(sort.lower, sort.upper, t))

  /**
   * Cast a term to an integer interval, with modulo semantics.
   */
  def cast2Interval(lower : IdealInt, upper : IdealInt, t : ITerm) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, lower <= upper)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    IFunApp(mod_cast, List(lower, upper, t))
  }

  /**
   * Cast a term to an unsigned bit-vector term.
   */
  def cast2UnsignedBV(bits : Int, t : ITerm) : ITerm = {
    val ModSort(lower, upper) = UnsignedBVSort(bits)
    IFunApp(mod_cast, List(lower, upper, t))
  }

  /**
   * Cast a term to a signed bit-vector term.
   */
  def cast2SignedBV(bits : Int, t : ITerm) : ITerm = {
    val ModSort(lower, upper) = SignedBVSort(bits)
    IFunApp(mod_cast, List(lower, upper, t))
  }

  //////////////////////////////////////////////////////////////////////////////

  class ShiftPredicate(name : String)
        extends SortedPredicate(name, 5) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      List(Sort.Integer, Sort.Integer, Sort.Integer, Sort.Integer,
           ModSort(lower, upper))
    }
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      val (lower, upper) = getLowerUpper(arguments)
      List(Sort.Integer, Sort.Integer, Sort.Integer, Sort.Integer,
           ModSort(lower, upper))
    }
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  class ShiftFunction(name : String, val toPredicate : ShiftPredicate)
        extends SortedIFunction(name, 4, true, false) {
    private val argSorts =
      List(Sort.Integer, Sort.Integer, Sort.Integer, Sort.Integer)
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      (argSorts, ModSort(lower, upper))
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      val (lower, upper) = getLowerUpper(arguments)
      (argSorts, ModSort(lower, upper))
    }
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
  }

  val _l_shift_cast = new ShiftPredicate("l_shift_cast")

  /**
   * Function for multiplying any number <code>t</code> with <code>2^n</code>
   * and mapping to an interval [lower, upper].
   * The function is applied as <code>l_shift_cast(lower, upper, t, n)</code>.
   */
  val l_shift_cast = new ShiftFunction("l_shift_cast", _l_shift_cast)

  /**
   * Shift the term <code>shifted</code> a number of bits to the left,
   * staying within the given sort.
   */
  def shiftLeft(sort : ModSort, shifted : ITerm, bits : ITerm) : ITerm =
    IFunApp(l_shift_cast, List(sort.lower, sort.upper, shifted, bits))

  val _r_shift_cast = new ShiftPredicate("r_shift_cast")

  /**
   * Function for dividing any number <code>t</code> by <code>2^n</code>,
   * rounding towards negative, and mapping to an interval [lower, upper].
   * The function is applied as <code>r_shift_cast(lower, upper, t, n)</code>.
   */
  val r_shift_cast = new ShiftFunction("r_shift_cast", _r_shift_cast)

  /**
   * Shift the term <code>shifted</code> a number of bits to the right,
   * staying within the given sort.
   */
  def shiftRight(sort : ModSort, shifted : ITerm, bits : ITerm) : ITerm =
    IFunApp(r_shift_cast, List(sort.lower, sort.upper, shifted, bits))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generic class to represent families of functions, indexed by a vector of
   * bit-widths.
   */
  abstract class IndexedBVOp(_name : String, indexArity : Int, bvArity : Int,
                             functional : Boolean = false)
           extends SortedIFunction(_name, indexArity + bvArity, true,
                                   !functional) {

    /**
     * Given the vector of indexes, compute the argument and the result
     * sorts of the function.
     */
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort)

    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val indexes =
        for (IIntLit(IdealInt(n)) <- arguments take indexArity) yield n
      computeSorts(indexes)
    }
    
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      val indexes =
        for (lc <- arguments take indexArity)
        yield lc.asInstanceOf[LinearCombination0].constant.intValueSafe
      computeSorts(indexes)
    }
    
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
    
    def toPredicate : SortedPredicate =
      new SortedPredicate(_name, indexArity + bvArity + 1) {
        def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
          val indexes =
            for (IIntLit(IdealInt(n)) <- arguments take indexArity) yield n
          val (args, res) = computeSorts(indexes)
          args ++ List(res)
        }
        
        def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
          val indexes =
            for (lc <- arguments take indexArity)
            yield lc.asInstanceOf[LinearCombination0].constant.intValueSafe
          val (args, res) = computeSorts(indexes)
          args ++ List(res)
        }
        
        override def sortConstraints(arguments : Seq[Term])
                                    (implicit order : TermOrder) : Formula =
          argumentSorts(arguments).last membershipConstraint arguments.last
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  // Arguments: N1, N2, number mod 2^N1, number mod 2^N2
  // Result:    number mod 2^(N1 + N2)

  object BVConcat extends IndexedBVOp("bv_concat", 2, 2) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      (List(Sort.Integer, Sort.Integer,
            UnsignedBVSort(indexes(0)), UnsignedBVSort(indexes(1))),
       UnsignedBVSort(indexes(0) + indexes(1)))
    }
  }

  val bv_concat = BVConcat // X
  
  //////////////////////////////////////////////////////////////////////////////

  // Arguments: begin, end, number
  // Result:    number mod 2^(begin - end + 1)

  object BVExtract extends IndexedBVOp("bv_extract", 2, 1, functional = true) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      (List(Sort.Integer, Sort.Integer, Sort.Integer),
       UnsignedBVSort(indexes(0) - indexes(1) + 1))
    }
  }

  val bv_extract = BVExtract

  //////////////////////////////////////////////////////////////////////////////

  class BVNAryOp(_name : String, _arity : Int)
        extends IndexedBVOp(_name, 1, _arity) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      val sort = UnsignedBVSort(indexes.head)
      (Sort.Integer :: List.fill(_arity)(sort), sort)
    }
  }

  // Arguments: N, number mod 2^N
  // Result:    number mod 2^N
  val bv_not           = new BVNAryOp ("bv_not", 1) // X
  val bv_neg           = new BVNAryOp ("bv_neg", 1) // X

  // Arguments: N, number mod 2^N, number mod 2^N
  // Result:    number mod 2^N
  val bv_and           = new BVNAryOp ("bv_and", 2)
  val bv_or            = new BVNAryOp ("bv_or",  2)
  val bv_add           = new BVNAryOp ("bv_add", 2) // X
  val bv_sub           = new BVNAryOp ("bv_sub", 2) // X
  val bv_mul           = new BVNAryOp ("bv_mul", 2) // X (to be optimised)
  val bv_udiv          = new BVNAryOp ("bv_udiv",2) // X
  val bv_sdiv          = new BVNAryOp ("bv_sdiv",2)
  val bv_urem          = new BVNAryOp ("bv_urem",2) // partly
  val bv_srem          = new BVNAryOp ("bv_srem",2)
  val bv_smod          = new BVNAryOp ("bv_smod",2)
  val bv_shl           = new BVNAryOp ("bv_shl", 2) // partly
  val bv_lshr          = new BVNAryOp ("bv_lshr",2)
  val bv_ashr          = new BVNAryOp ("bv_ashr",2)

  val bv_xor           = new BVNAryOp ("bv_xor", 2)
  val bv_xnor          = new BVNAryOp ("bv_xnor",2)

  //////////////////////////////////////////////////////////////////////////////

  // Arguments: N, number mod 2^N, number mod 2^N
  // Result:    number mod 2
  object BVComp extends IndexedBVOp("bv_comp", 1, 2) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      val sort = UnsignedBVSort(indexes.head)
      (Sort.Integer :: List.fill(2)(sort), UnsignedBVSort(1))
    }
  }

  val bv_comp = BVComp

  //////////////////////////////////////////////////////////////////////////////

  // Arguments: N, number mod 2^N, number mod 2^N
  val bv_ult           = new Predicate("bv_ult", 3) // X
  val bv_ule           = new Predicate("bv_ule", 3) // X
  val bv_slt           = new Predicate("bv_slt", 3) // X
  val bv_sle           = new Predicate("bv_sle", 3) // X

  //////////////////////////////////////////////////////////////////////////////

  val functions = List(
    mod_cast,
    l_shift_cast,
    r_shift_cast,
    bv_concat,
    bv_extract,
    bv_not,
    bv_neg,
    bv_and,
    bv_or,
    bv_add,
    bv_sub,
    bv_mul,
    bv_udiv,
    bv_sdiv,
    bv_urem,
    bv_srem,
    bv_smod,
    bv_shl,
    bv_lshr,
    bv_ashr,
    bv_xor,
    bv_xnor,
    bv_comp
  )

  val otherPreds = List(bv_ult, bv_ule, bv_slt, bv_sle)

  val (functionalPredSeq, preAxioms, preOrder, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  private val _bv_extract = functionTranslation(bv_extract)

  // We only keep the functionality axiom for the bv_extract function
  val axioms =
    (Conjunction.conj(preAxioms, preOrder).iterator filter (
       _.predicates == Set(_bv_extract))).next

  val functionPredicateMapping = functions zip functionalPredSeq
  val functionalPredicates = functionalPredSeq.toSet

  val order = preOrder extendPred otherPreds

  val predicates = otherPreds ++ functionalPredSeq
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig: Signature.PredicateMatchConfig =
    (for (p <- predicates.toSet --
           List(_mod_cast, _l_shift_cast, _r_shift_cast, _bv_extract))
     yield (p -> Signature.PredicateMatchStatus.None)).toMap
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  override val singleInstantiationPredicates = predicates.toSet

  //////////////////////////////////////////////////////////////////////////////

  private case class VisitorArg(modN : Option[IdealInt],
                                boundVarRanges : List[(Option[IdealInt],
                                                       Option[IdealInt])],
                                underQuantifier : Boolean) {
    import IExpression._

    def setMod(n : IdealInt) =
      copy(modN = Some(n), underQuantifier = false)

    def addMod(n : IdealInt) = modN match {
      case Some(oldN) if (oldN divides n) =>
        this.notUnderQuantifier
      case _ =>
        this.setMod(n)
    }

    def multMod(factor : IdealInt, localMod : IdealInt) = modN match {
      case Some(oldN) => {
        val prod = oldN * factor
        if (prod divides localMod)
          setMod(prod)
        else
          setMod(localMod)
      }
      case None =>
        setMod(localMod)
    }

    def divideMod(divisor : IdealInt) = modN match {
      case Some(oldN) => {
        val g = oldN gcd divisor
        if (g > IdealInt.ONE)
          setMod(oldN / g)
        else
          this.notUnderQuantifier
      }
      case _ =>
        this.notUnderQuantifier
    }

    def noMod =
      if (modN.isDefined || underQuantifier)
        copy(modN = None, underQuantifier = false)
      else
        this

    def pushVar =
      copy(boundVarRanges = (None, None) :: boundVarRanges,
           underQuantifier = true)

    def notUnderQuantifier =
      if (underQuantifier)
        copy(underQuantifier = false)
      else
        this

    def collectVariableRanges(f : IFormula) = {
      var ranges = boundVarRanges

      def collectRanges(f : IFormula, neg : Boolean) : Unit = f match {
        case INot(subF) =>
          collectRanges(subF, !neg)
        case Conj(left, right) if !neg => {
          collectRanges(left, neg)
          collectRanges(right, neg)
        }
        case Disj(left, right) if neg => {
          collectRanges(left, neg)
          collectRanges(right, neg)
        }
        case Geq(IVariable(ind), IIntLit(value)) if !neg => {
          val (oldL, oldU) =
            ranges(ind)
          ranges =
            ranges.updated(ind, (Some((oldL getOrElse value) max value), oldU))
        }
        case Geq(IIntLit(value), IVariable(ind)) if !neg => {
          val (oldL, oldU) =
            ranges(ind)
          ranges =
            ranges.updated(ind, (oldL, Some((oldU getOrElse value) min value)))
        }
        case _ =>
          // nothing
      }

      collectRanges(f, false)
      copy(boundVarRanges = ranges, underQuantifier = false)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
 
  private object VisitorRes {

    def apply(const : IdealInt) : VisitorRes =
      VisitorRes(IIntLit(const), const, const)

    def apply(e : IExpression) : VisitorRes =
      VisitorRes(e, null, null)

    def update(t : IExpression, subres : Seq[VisitorRes]) : VisitorRes = {
      if (subres.isEmpty)
        deriveBounds(t, subres)
      else
        deriveBounds(t update (subres map (_.res)), subres)
    }

    def deriveBounds(t : IExpression,
                     subres : Seq[VisitorRes]) : VisitorRes = t match {
      case _ : IFormula =>
        VisitorRes(t, null, null)

      case IIntLit(value) =>
        VisitorRes(t, value, value)

      case _ : IPlus => {
        val Seq(VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        val newLB = if (lb1 == null || lb2 == null) null else (lb1 + lb2)
        val newUB = if (ub1 == null || ub2 == null) null else (ub1 + ub2)
        VisitorRes(t, newLB, newUB)
      }

      case ITimes(coeff, _) => {
        val Seq(VisitorRes(_, lb, ub)) = subres
        if (coeff.signum >= 0)
          VisitorRes(t,
                     if (lb == null) null else (lb * coeff),
                     if (ub == null) null else (ub * coeff))
        else
          VisitorRes(t,
                     if (ub == null) null else (ub * coeff),
                     if (lb == null) null else (lb * coeff))
      }

      case _ : ITermITE => {
        val Seq(_, VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        val newLB = if (lb1 == null || lb2 == null) null else (lb1 min lb2)
        val newUB = if (ub1 == null || ub2 == null) null else (ub1 max ub2)
        VisitorRes(t, newLB, newUB)
      }

      case IFunApp(MulTheory.Mul(), _) => {
        val Seq(VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        if (lb1 == null || lb2 == null || ub1 == null || ub2 == null) {
          VisitorRes(t, null, null)
        } else {
          val p1 = lb1 * lb2
          val p2 = lb1 * ub2
          val p3 = ub1 * lb2
          val p4 = ub1 * ub2
          VisitorRes(t, p1 min p2 min p3 min p4, p1 max p2 max p3 max p4)
        }
      }

      case _ : IConstant |
           _ : IFunApp => (Sort sortOf t.asInstanceOf[ITerm]) match {
        case ModSort(lower, upper) =>
          VisitorRes(t, lower, upper)
        case Sort.Interval(lower, upper) =>
          VisitorRes(t, lower getOrElse null, upper getOrElse null)
        case _ =>
          VisitorRes(t, null, null)
      }

      case _ =>
        VisitorRes(t, null, null)
    }
  }

  private case class VisitorRes(res : IExpression,
                                lowerBound : IdealInt,   // maybe null
                                upperBound : IdealInt) { // maybe null
    import IExpression._

    def resTerm = res.asInstanceOf[ITerm]

    def modCast(lower : IdealInt, upper : IdealInt,
                ctxt : VisitorArg) : VisitorRes =
      modCastHelp(lower, upper, ctxt) match {
        case null =>
          VisitorRes(mod_cast(lower, upper, resTerm), lower, upper)
        case res =>
          res
      }

    def modCastPow2(bits : Int, ctxt : VisitorArg) : VisitorRes =
      modCast(IdealInt.ZERO, pow2MinusOne(bits), ctxt)

    def modCastSignedPow2(bits : Int, ctxt : VisitorArg) : VisitorRes = {
      val ModSort(lower, upper) = SignedBVSort(bits)
      modCast(lower, upper, ctxt)
    }

    def modCastHelp(lower : IdealInt, upper : IdealInt,
                    ctxt : VisitorArg) : VisitorRes = {
      val modulus = upper - lower + IdealInt.ONE
      ctxt.modN match {
        case Some(n) if (n divides modulus) =>
          this
        case _ =>
          if (lowerBound == null || upperBound == null) {
            null // mod_cast is needed!
          } else {
            val lowerFactor = (lowerBound - lower) / modulus
            val upperFactor = -((upper - upperBound) / modulus)
            if (lowerFactor == upperFactor) {
              if (lowerFactor.isZero) {
                this
              } else {
                val corr = lowerFactor * modulus
                if (isConstant)
                  VisitorRes(lowerBound - corr)
                else
                  VisitorRes(resTerm - corr, lowerBound - corr, upperBound - corr)
              }
            } else {
              null // mod_cast is needed!
            }
          }
      }
    }

    def isConstant : Boolean =
      lowerBound != null && upperBound != null && lowerBound == upperBound

    def +(that : VisitorRes) : VisitorRes =
      VisitorRes.deriveBounds(IPlus(this.resTerm, that.resTerm),
                              List(this, that))

    def +(num : IdealInt) : VisitorRes =
      if (num.isZero)
        this
      else
        this + VisitorRes(num, num, num)

    def *(coeff : IdealInt) : VisitorRes =
      if (coeff.isOne)
        this
      else
        VisitorRes.deriveBounds(ITimes(coeff, resTerm), List(this))

    def *(that : VisitorRes) : VisitorRes =
      VisitorRes.deriveBounds(IFunApp(MultTheory.mul,
                                      List(this.resTerm, that.resTerm)),
                              List(this, that))

    def eDiv(divisor : IdealInt) : VisitorRes = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, divisor.signum > 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      VisitorRes(MultTheory.eDiv(resTerm, divisor),
                 lowerBound match {
                   case null               => null
                   case b if b.signum <= 0 => b / divisor
                   case _                  => IdealInt.ZERO
                 },
                 upperBound match {
                   case null               => null
                   case b if b.signum >= 0 => b / divisor
                   case _                  => IdealInt.ZERO
                 })
    }

    def lowerBoundOrElse(that : IdealInt) : IdealInt = lowerBound match {
      case null => that
      case b    => b
    }

    def lowerBoundMin(minimum : IdealInt) : IdealInt = lowerBound match {
      case null => minimum
      case b    => b max minimum
    }

    def upperBoundOrElse(that : IdealInt) : IdealInt = upperBound match {
      case null => that
      case b    => b
    }

    def upperBoundMax(maximum : IdealInt) : IdealInt = upperBound match {
      case null => maximum
      case b    => b min maximum
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def evalFun(f : IFunApp) : Option[ITerm] =
    if (f.args forall (isLit _)) {
      val sort = Sort sortOf f
      val res = Preproc.visit(f, VisitorArg(None, List(), false))
      if (res.isConstant)
        Some(IIntLit(res.lowerBound))
      else
        None
    } else {
      None
    }

  override def evalPred(a : IAtom) : Option[Boolean] =
    if (a.args forall (isLit _)) {
      Preproc.visit(a, VisitorArg(None, List(), false)).res match {
        case IBoolLit(v) => Some(v)
        case _           => None
      }
    } else {
      None
    }

  private def isLit(t : ITerm) : Boolean = t match {
    case _ : IIntLit                                         => true
    case IFunApp(`mod_cast`,
                 Seq(_ : IIntLit, _ : IIntLit, _ : IIntLit)) => true
    case _                                                   => false
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor called during pre-processing, to translate
   * bit-vector operations to a basic set of operations
   * (mod_cast, ...) and simplify.
   */
  private object Preproc extends CollectingVisitor[VisitorArg, VisitorRes] {
    import IExpression._

    override def preVisit(t : IExpression,
                          ctxt : VisitorArg) : PreVisitResult = t match {
      case _ : IQuantified | _ : IEpsilon =>
        UniSubArgs(ctxt.pushVar)
      case Conj(left, _) if ctxt.underQuantifier =>
        SubArgs(List(ctxt.notUnderQuantifier,
                     ctxt collectVariableRanges left))
      case Disj(left, _) if ctxt.underQuantifier =>
        SubArgs(List(ctxt.notUnderQuantifier,
                     ctxt collectVariableRanges ~left))

      case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt addMod (upper - lower + IdealInt.ONE)))

      case IFunApp(`l_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt addMod (upper - lower + IdealInt.ONE),
                     ctxt.noMod))

      case IFunApp(`bv_extract`,
                   Seq(IIntLit(IdealInt(begin)), IIntLit(IdealInt(end)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt.multMod(pow2(end), pow2(begin + 1))))

      case IFunApp(`bv_neg` | `bv_add` | `bv_sub` | `bv_mul` | `bv_srem`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        // TODO: handle bit-width argument correctly
        UniSubArgs(ctxt addMod pow2(n))

      case IFunApp(`bv_shl` | `bv_ashr`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt addMod pow2(n), ctxt.noMod))

      case IAtom(`bv_slt` | `bv_sle`,
                 Seq(IIntLit(IdealInt(n)), _*)) =>
        UniSubArgs(ctxt addMod pow2(n))

      case _ : IPlus | IFunApp(MulTheory.Mul(), _) => // IMPROVE
        UniSubArgs(ctxt.notUnderQuantifier)
      case ITimes(coeff, _) =>
        UniSubArgs(ctxt divideMod coeff)

      case _ : ITermITE =>
        SubArgs(List(ctxt.noMod,
                     ctxt.notUnderQuantifier, ctxt.notUnderQuantifier))

      case _ =>
        UniSubArgs(ctxt.noMod)
    }

    def doExtract(start : Int, end : Int, arg : ITerm, argBits : Int) : ITerm =
      if (start == argBits - 1 && end == 0) {
        arg
      } else arg match {
        case IIntLit(argVal) =>
          evalExtract(start, end, argVal)
        case arg =>
          IFunApp(bv_extract, Vector(start, end, arg))
      }

    ////////////////////////////////////////////////////////////////////////////

    def postVisit(t : IExpression,
                  ctxt : VisitorArg, subres : Seq[VisitorRes]) : VisitorRes =
      t match {
        case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _)) =>
          subres.last.modCastHelp(lower, upper, ctxt) match {
            case null => VisitorRes.update(t, subres)
            case res  => res
          }

        case IFunApp(`bv_extract`, Seq(IIntLit(IdealInt(start)),
                                       IIntLit(IdealInt(end)), _*)) =>
          if (subres(2).isConstant)
            VisitorRes(evalExtract(start, end, subres(2).lowerBound))
          else
            VisitorRes.update(t, subres)

        case IFunApp(`bv_concat`, Seq(IIntLit(IdealInt(bits1)),
                                      IIntLit(IdealInt(bits2)), _*)) =>
          if (subres(2).isConstant && subres(3).isConstant) {
            VisitorRes(subres(2).lowerBound * pow2(bits2) +
                       subres(3).lowerBound)
          } else {
            val sort = UnsignedBVSort(bits1+bits2)

            // We create a new variable v(0) which is existentially
            // quantified, representing the result of the concat

            val bv1lhs = bv_extract(bits1+bits2-1, bits2, v(0))
            val bv1rhs = VariableShiftVisitor(subres(2).resTerm, 0, 1)
            val bv1 = (bv1lhs === bv1rhs)

            val bv2lhs = bv_extract(bits2-1, 0, v(0))
            val bv2rhs = VariableShiftVisitor(subres(3).resTerm, 0, 1)
            val bv2 = (bv2lhs === bv2rhs)

            val res = sort.eps(bv1 & bv2)

            VisitorRes(res,
                       (subres(2).lowerBoundOrElse(IdealInt.ZERO) * pow2(bits2)) +
                         subres(3).lowerBoundOrElse(IdealInt.ZERO),
                       (subres(2).upperBoundOrElse(pow2(bits1)) * pow2(bits2)) +
                         subres(3).upperBoundOrElse(pow2(bits2)))
          }

        case IFunApp(`bv_not`, Seq(IIntLit(IdealInt(bits)), _)) =>
          if (subres(1).isConstant) {
            VisitorRes(pow2MinusOne(bits) - subres(1).lowerBound)
          } else {
            val sort = UnsignedBVSort(bits)

            val rawArg = subres(1).resTerm
            val simple = isSimpleTerm(rawArg)

            val (arg, resTerm) =
              if (simple)
                (VariableShiftVisitor(rawArg, 0, 1), v(0))
              else
                (v(0), v(1))

            val resultDef =
              and(for (i <- 0 until bits) yield {
                eqZero(doExtract(i, i, arg, bits) +
                       doExtract(i, i, resTerm, bits) +
                       IdealInt.MINUS_ONE)
              })

            val res =
              if (simple)
                sort.eps(resultDef)
              else
                sort.eps(ex(v(0) === VariableShiftVisitor(rawArg, 0, 2) &
                            resultDef))

            VisitorRes(res,
                       sort.upper - (subres(1) upperBoundMax sort.upper),
                       sort.upper - (subres(1) lowerBoundMin IdealInt.ZERO))
          }

        case IFunApp(`bv_neg`, Seq(IIntLit(IdealInt(bits)), _)) =>
          (subres.last * IdealInt.MINUS_ONE).modCastPow2(bits, ctxt)

        case IFunApp(`bv_add`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + subres(2)).modCastPow2(bits, ctxt)

        case IFunApp(`bv_sub`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + (subres(2) * IdealInt.MINUS_ONE)).modCastPow2(bits, ctxt)

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_mul`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound *
                         subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (true, false) =>
              (subres(2) * subres(1).lowerBound).modCastPow2(bits, ctxt)
            case (false, true) =>
              (subres(1) * subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (false, false) =>
              (subres(1) * subres(2)).modCastPow2(bits, ctxt)
          }

        // TODO: move this clause to the multiplication theory?
        case IFunApp(MulTheory.Mul(), Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound *
                         subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (true, false) =>
              subres(2) * subres(1).lowerBound
            case (false, true) =>
              subres(1) * subres(2).lowerBound
            case (false, false) =>
              VisitorRes.update(t, subres)
          }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`l_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
          if (subres(3).isConstant)
            (subres(2) * pow2(subres(3).lowerBound max IdealInt.ZERO))
                .modCast(lower, upper, ctxt)
          else
            VisitorRes.update(t, subres)

        case IFunApp(`r_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
          if (subres(3).isConstant) {
            val denom = pow2(subres(3).lowerBound max IdealInt.ZERO)
            subres(2).eDiv(denom).modCast(lower, upper, ctxt)
          } else {
            VisitorRes.update(t, subres)
          }

        ////////////////////////////////////////////////////////////////////////

        // TODO: Translate to extract instead!
        case IFunApp(`bv_shl`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            (subres(1) * pow2(subres(2).lowerBound.intValueSafe))
              .modCastPow2(bits, ctxt)
          } else {
            val upper = pow2MinusOne(bits)
            VisitorRes(l_shift_cast(IdealInt.ZERO, upper,
                                    subres(1).resTerm, subres(2).resTerm),
                       IdealInt.ZERO, upper)
          }

        case IFunApp(`bv_lshr`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            subres(2).lowerBound match {
              case IdealInt.ZERO =>
                subres(1)
              case shift if shift.signum < 0 =>
                throw new Exception("negative shift")
              case IdealInt(shift) if shift < bits => {
                val divisor = pow2(shift)
                VisitorRes(
                  doExtract(bits-1, shift, subres(1).resTerm, bits),
                  subres(1).lowerBoundMin(IdealInt.ZERO) / divisor,
                  subres(1).upperBoundMax(pow2MinusOne(bits+1)) / divisor)
              }
              case _ =>
                VisitorRes(IdealInt.ZERO)
            }
          } else {
            val upper = pow2MinusOne(bits)
            VisitorRes(r_shift_cast(IdealInt.ZERO, upper,
                                    subres(1).resTerm, subres(2).resTerm),
                       IdealInt.ZERO, upper)
          }

        case IFunApp(`bv_ashr`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            subres(2).lowerBound match {
              case IdealInt.ZERO =>
                subres(1).modCastPow2(bits, ctxt)
              case shift if shift.signum < 0 =>
                throw new Exception("negative shift")
              case IdealInt(shift) =>
                subres(1).modCastSignedPow2(bits, ctxt.noMod)
                         .eDiv(pow2(shift))
                         .modCastPow2(bits, ctxt)
            }
          } else {
            val ModSort(lower, upper) = SignedBVSort(bits)
            VisitorRes(r_shift_cast(
                         lower, upper,
                         subres(1).modCastSignedPow2(bits, ctxt.noMod).resTerm,
                         subres(2).resTerm),
                       lower, upper).modCastPow2(bits, ctxt)
          }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_and`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)

          def oneConstant(arg : VisitorRes, pattern : IdealInt) : VisitorRes =
            runlengths(pattern) match {
              case Seq(_) => {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                // Pattern must be constantly zero
                Debug.assertInt(AC, pattern.isZero)
                //-END-ASSERTION-///////////////////////////////////////////////
                VisitorRes(IdealInt.ZERO)
              }
              case Seq(0, length) => {
                // pattern starting with a single block of ones
                VisitorRes(
                  doExtract(length - 1, 0, arg.resTerm, bits),
                  IdealInt.ZERO, pattern)
              }

              case preLens => {
                // multiple blocks of zeros, handle using an epsilon term
                val lens = completedRunlengths(preLens, bits)

                var offset : Int = 0
                var bit = true
                
                val resultDef =
                  and(for (len <- lens) yield {
                        bit = !bit
                        if (len > 0) {
                          offset = offset + len
                          doExtract(offset-1, (offset-len), v(1), bits) === 
                          (if (bit)
                             doExtract(offset-1, (offset-len), v(0), bits)
                           else
                             i(0))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  sort.eps(
                    ex(v(0) === VariableShiftVisitor(arg.resTerm, 0, 2) &
                       resultDef))

                VisitorRes(res, IdealInt.ZERO, pattern)
              }
            }

          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound & subres(2).lowerBound)
            case (true, false) =>
              oneConstant(subres(2), subres(1).lowerBound)
            case (false, true) =>
              oneConstant(subres(1), subres(2).lowerBound)

            case (false, false) => {
              val resultDef = 
                and(for (i <- 0 until bits) yield{
                  val res = doExtract(i, i, v(2), bits)
                  val lhs = doExtract(i, i, v(1), bits)
                  val rhs = doExtract(i, i, v(0), bits)
                  (res <= lhs) & (res <= rhs) & (res >= lhs + rhs - 1)
                })
              val res =
                sort.eps(ex(ex(
                  v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                  v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                  resultDef)))
              VisitorRes(res,
                         IdealInt.ZERO,
                         (subres(1) upperBoundMax sort.upper) min
                           (subres(2) upperBoundMax sort.upper))
            }

          }
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_or`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)

          def oneConstant(arg : VisitorRes, pattern : IdealInt) : VisitorRes =
            runlengths(pattern) match {
              case Seq(_) => {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                // Pattern must be constantly zero
                Debug.assertInt(AC, pattern.isZero)
                //-END-ASSERTION-///////////////////////////////////////////////
                arg
              }
              case Seq(offset, length) if offset + length == bits => {
                // pattern ending with a single block of ones
                VisitorRes(
                  doExtract(offset-1, 0, arg.resTerm, bits) + pattern,
                  pattern, pow2MinusOne(bits))
              }
              
              case preLens => {
                // multiple blocks of zeros, handle using an epsilon term
                val lens = completedRunlengths(preLens, bits)

                var offset : Int = 0
                var bit = true

                val resultDef =
                  and(for (len <- lens) yield {
                        bit = !bit
                        if (len > 0) {
                          offset = offset + len
                          doExtract(offset-1, offset-len, v(1), bits) ===
                          (if (bit)
                             i(pow2MinusOne(len))
                           else
                             doExtract(offset-1, offset - len, v(0), bits))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  sort.eps(
                    ex(v(0) === VariableShiftVisitor(arg.resTerm, 0, 2) &
                       resultDef))

                VisitorRes(res, pattern, pow2MinusOne(bits))
              }
            }

          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound | subres(2).lowerBound)
            case (true, false) =>
              oneConstant(subres(2), subres(1).lowerBound)
            case (false, true) =>
              oneConstant(subres(1), subres(2).lowerBound)

            case (false, false) => {
              val resultDef = 
                and(for (i <- 0 until bits) yield{
                  val res = doExtract(i, i, v(2), bits)
                  val lhs = doExtract(i, i, v(1), bits)
                  val rhs = doExtract(i, i, v(0), bits)
                  (res >= lhs) & (res >= rhs) & (res <= lhs + rhs)
                })
              val res =
                sort.eps(ex(ex(
                    v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                    v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                    resultDef)))
    
              VisitorRes(res,
                         (subres(1) lowerBoundMin IdealInt.ZERO) max
                           (subres(2) lowerBoundMin IdealInt.ZERO),
                         sort.upper)
            }

          }
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_xor`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val resultDef = 
            and(for (i <- 0 until bits) yield{
              val res = doExtract(i, i, v(2), bits)
              val lhs = doExtract(i, i, v(1), bits)
              val rhs = doExtract(i, i, v(0), bits)
              import TerForConvenience._
              mod_cast(0, 1, lhs+rhs) === res
            })
          val res =
            sort.eps(ex(ex(
                v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                resultDef)))
          VisitorRes(res, IdealInt.ZERO, sort.upper)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_comp`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(1).isConstant && subres(2).isConstant) {
            VisitorRes(if (subres(1).lowerBound == subres(2).lowerBound)
                         IdealInt.ONE
                       else
                         IdealInt.ZERO)
          } else {
            // could be optimised further: handle cases where the bounds imply
            // that the terms have different values
            VisitorRes(ite(subres(1).resTerm === subres(2).resTerm,
                           IdealInt.ONE, IdealInt.ZERO),
                       IdealInt.ZERO, IdealInt.ONE)
          }

        ////////////////////////////////////////////////////////////////////////

        // TODO: special treatment for constant denominators?
        case IFunApp(`bv_udiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val ModSort(lower, upper) = UnsignedBVSort(bits)
          VisitorRes(ite(subres(2).resTerm === 0,
                         upper,
                         MultTheory.eDiv(subres(1).resTerm, subres(2).resTerm)),
                     lower, upper)
        }
        // TODO: special treatment for constant denominators?
        case IFunApp(`bv_urem`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          VisitorRes(ite(subres(2).resTerm === 0,
                         subres(1).resTerm,
                         MultTheory.eMod(subres(1).resTerm, subres(2).resTerm)),
                     IdealInt.ZERO, subres(1).upperBound)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_sdiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val ModSort(_, unsUpper) = sort
          val ModSort(sLower, sUpper) = SignedBVSort(bits)

          val modulus = sort.modulus

/*
          val num = subres(1).resTerm
          val negNum = -num + modulus
          val denom = subres(2).resTerm
          val negDenom = -denom + modulus
          val v0Denom = MultTheory.mult(v(0), denom)
          val v0NegDenom = MultTheory.mult(v(0), negDenom)

          val res = VisitorRes(
            eps(((denom === 0) &
                   (v(0) === ite(num > sUpper, IdealInt.ONE, unsUpper))) |
                ((num <= sUpper) & (denom > 0) & (denom <= sUpper) &
                   (v0Denom <= num) & (v0Denom > num - denom)) |
                ((num > sUpper) & (denom > 0) & (denom <= sUpper) &
                   (-v0Denom <= negNum) & (-v0Denom > negNum - denom)) |
                ((num <= sUpper) & (denom > sUpper) &
                   (-v0Denom <= num) & (-v0Denom > num - negDenom)) |
                ((num > sUpper) & (denom > sUpper) &
                   (v0NegDenom <= negNum) & (v0NegDenom > negNum - negDenom))))
*/

          val resVar = v(3)

          val (num, numDef) =
            VariableShiftVisitor(subres(1).resTerm, 0, 4) match {
              case SimpleTerm(rawNum) => (rawNum, i(true))
              case rawNum             => (v(0), v(0) === rawNum)
            }

          val negNum = -num + modulus

          val (denom, denomDef) =
            VariableShiftVisitor(subres(2).resTerm, 0, 4) match {
              case SimpleTerm(rawDenom) => (rawDenom, i(true))
              case rawDenom             => (v(1), v(1) === rawDenom)
            }

          val negDenom = -denom + modulus

          val (timesDenom, timesDenomDef) =
            MultTheory.mult(resVar, denom) match {
              case SimpleTerm(t) => (t, i(true))
              case t             => (v(2), v(2) === t)
            }

          val negTimesDenom = -timesDenom + (resVar * modulus)

          val VisitorRes(_, denomLower, denomUpper) = subres(2)
          val denomMightBeZero =
            denomLower == null || denomLower.signum <= 0
          val denomMightBePositive =
            !(denomLower != null && denomLower > sUpper ||
              denomUpper != null && denomUpper.signum <= 0)
          val denomMightBeNegative =
            denomUpper == null || denomUpper > sUpper

          val res = VisitorRes(
            eps(ex(ex(ex(
                numDef &&& denomDef &&& timesDenomDef &&&
                ((if (denomMightBeZero)
                    (denom === 0) &
                      (resVar === ite(num > sUpper, IdealInt.ONE, unsUpper))
                  else
                    i(false)) |||
                 (if (denomMightBePositive)
                    ((num <= sUpper) & (denom > 0) & (denom <= sUpper) &
                       (timesDenom <= num) &
                       (timesDenom > num - denom)) |
                    ((num > sUpper) & (denom > 0) & (denom <= sUpper) &
                       (-timesDenom <= negNum) &
                       (-timesDenom > negNum - denom))
                  else
                    i(false)) |||
                 (if (denomMightBeNegative)
                    ((num <= sUpper) & (denom > sUpper) &
                       (-timesDenom <= num) &
                       (-timesDenom > num - negDenom)) |
                    ((num > sUpper) & (denom > sUpper) &
                       (negTimesDenom <= negNum) &
                       (negTimesDenom > negNum - negDenom))
                  else
                    i(false))))))),
            sLower, unsUpper)

          res.modCastPow2(bits, ctxt)
        }

/*
        case IFunApp(`bv_sdiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val ModSort(lower, upper) = UnsignedBVSort(bits)
          val noModCtxt = ctxt.noMod
          val numMod = subres(1).modCastSignedPow2(bits, noModCtxt).resTerm
          val divTerm =
            MultTheory.tDiv(
                  numMod,
                  subres(2).modCastSignedPow2(bits, noModCtxt).resTerm)
          VisitorRes(
            ite(subres(2).resTerm === 0,
                ite(numMod < 0, IdealInt.ONE, upper),
                VisitorRes(divTerm).modCastPow2(bits, ctxt).resTerm),
            lower, upper)
        }
*/

        ////////////////////////////////////////////////////////////////////////

        // TODO: special treatment for constant denominators?
        case IFunApp(`bv_srem`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val noModCtxt = ctxt.noMod
          val ModSort(lower, upper) = SignedBVSort(bits)
          VisitorRes(
            ite(subres(2).resTerm === 0,
                subres(1).resTerm,
                MultTheory.tMod(
                  subres(1).modCastSignedPow2(bits, noModCtxt).resTerm,
                  subres(2).modCastSignedPow2(bits, noModCtxt).resTerm)),
            lower, upper).modCastPow2(bits, ctxt)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_smod`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val ModSort(_, unsUpper) = sort
          val ModSort(sLower, sUpper) = SignedBVSort(bits)

          val modulus = sort.modulus

          val (num, numDef) =
            VariableShiftVisitor(subres(1).resTerm, 0, 5) match {
              case SimpleTerm(rawNum) => (rawNum, i(true))
              case rawNum             => (v(0), v(0) === rawNum)
            }

          val (denom, denomDef) =
            VariableShiftVisitor(subres(2).resTerm, 0, 5) match {
              case SimpleTerm(rawDenom) => (rawDenom, i(true))
              case rawDenom             => (v(1), v(1) === rawDenom)
            }

          val strideVar = v(3)
          val resVar = v(4)

          val (multPos, multPosDef) =
            MultTheory.mult(strideVar, denom) match {
              case SimpleTerm(t) => (t, i(true))
              case t             => (v(2), v(2) === t)
            }

          val multNeg = -multPos + (strideVar * modulus)

          val VisitorRes(_, denomLower, denomUpper) = subres(2)
          val denomMightBeZero =
            denomLower == null || denomLower.signum <= 0
          val denomMightBePositive =
            !(denomLower != null && denomLower > sUpper ||
              denomUpper != null && denomUpper.signum <= 0)
          val denomMightBeNegative =
            denomUpper == null || denomUpper > sUpper

          val res = VisitorRes(
            eps(ex(ex(ex(ex(
              numDef &&& denomDef &&& multPosDef &&&
              ((if (denomMightBeZero)
                  denom === 0 & resVar === num
                else
                  i(false)) |||
               (if (denomMightBePositive)
                  (num <= sUpper & denom > 0 & denom <= sUpper &
                   num === multPos + resVar &
                   resVar >= 0 & resVar < denom) |
                  (num > sUpper & denom > 0 & denom <= sUpper &
                   -num + modulus === multPos - resVar + denom &
                   resVar >= 0 & resVar < denom)
                else
                  i(false)) |||
               (if (denomMightBeNegative)
                  (num <= sUpper & denom > sUpper &
                   num === multNeg + resVar &
                   resVar <= 0 & resVar > denom - modulus) |
                  (num > sUpper & denom > sUpper &
                   -num + modulus === multNeg - resVar &
                   resVar <= 0 & resVar > denom - modulus)
                else
                  i(false)))
            ))))),
            sLower, sUpper)

          res.modCastPow2(bits, ctxt)
        }

        ////////////////////////////////////////////////////////////////////////

        case IAtom(`bv_ult`, _) =>
          if (subres(1).isConstant && subres(2).isConstant)
            VisitorRes(subres(1).lowerBound < subres(2).lowerBound)
          else
            VisitorRes(subres(1).resTerm < subres(2).resTerm)
 
        case IAtom(`bv_ule`, _) =>
          if (subres(1).isConstant && subres(2).isConstant)
            VisitorRes(subres(1).lowerBound <= subres(2).lowerBound)
          else
            VisitorRes(subres(1).resTerm <= subres(2).resTerm)

        case IAtom(`bv_slt`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant &&
              subres(2).modCastSignedPow2(bits, ctxt).lowerBound.isZero) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(1).modCastPow2(bits, ctxt).resTerm > mid)
          } else if (subres(1).isConstant &&
                     subres(1).modCastSignedPow2(bits, ctxt)
                              .lowerBound.isMinusOne) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(2).modCastPow2(bits, ctxt).resTerm <= mid)
          } else {
            VisitorRes(subres(1).modCastSignedPow2(bits, ctxt).resTerm <
                       subres(2).modCastSignedPow2(bits, ctxt).resTerm)
          }

        case IAtom(`bv_sle`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant &&
              subres(2).modCastSignedPow2(bits, ctxt).lowerBound.isMinusOne) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(1).modCastPow2(bits, ctxt).resTerm > mid)
          } else if (subres(1).isConstant &&
                     subres(1).modCastSignedPow2(bits, ctxt)
                              .lowerBound.isZero) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(2).modCastPow2(bits, ctxt).resTerm <= mid)
          } else {
            VisitorRes(subres(1).modCastSignedPow2(bits, ctxt).resTerm <=
                       subres(2).modCastSignedPow2(bits, ctxt).resTerm)
          }

        case t =>
          VisitorRes.update(t, subres)
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) =
    (Preproc.visit(f,
        VisitorArg(None, List(), false)).res.asInstanceOf[IFormula],
     signature)

  //////////////////////////////////////////////////////////////////////////////

  private val bits2RangeCache =
    new LRUCache[LinearCombination, LinearCombination](256)

  private def bits2Range(lc : LinearCombination) : LinearCombination =
    bits2RangeCache(lc) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, lc.isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val bits = lc.constant.intValueSafe
      LinearCombination(pow2MinusOne(bits))
    }

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    import TerForConvenience._

//    println("init: " + f)

    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case BVPred(`bv_concat` |
                    `bv_not` | `bv_neg` | `bv_add` | `bv_sub` | `bv_mul` |
                    `bv_udiv` | `bv_urem` |
                    `bv_sdiv` | `bv_srem` | `bv_srem` |
                    `bv_shl`) =>
          throw new Exception("unexpected function " + a.pred)

        case `bv_ult` | `bv_ule` | `bv_slt` | `bv_sle` =>
          throw new Exception("unexpected predicate " + a.pred)

/*
        case `_bv_extract` => { // old version
          val bits1 =
            a(0).asInstanceOf[LinearCombination0].constant.intValueSafe -
            a(1).asInstanceOf[LinearCombination0].constant.intValueSafe + 1
          val bits2 =
            a(1).asInstanceOf[LinearCombination0].constant.intValueSafe

          val castSort = UnsignedBVSort(bits1 + bits2)
          val remSort =  UnsignedBVSort(bits2)

          val subst = VariableShiftSubst(0, 1, order)
          val pred = _mod_cast(List(l(0), l(castSort.upper),
                                    subst(a(2)),
                                    subst(a(3))*remSort.modulus + v(0)))

          if (negated)
            existsSorted(List(remSort), pred)
          else
            // forall int v0, BV[bits2] v1.
            //   mod_cast(a(3), v0) => a(4)*modulus + v1 != v0
            // <=>
            // forall int v0, BV[bits2] v1.
            //   mod_cast(a(3), a(4)*modulus + v0) => v1 != v0
            // <=>
            // forall int v0.
            //   mod_cast(a(3), a(4)*modulus + v0) => v0 \not\in BV[bits2]
            forall(pred ==>
                     Conjunction.negate(remSort membershipConstraint v(0),
                                        order))
        }
 */

        case `_mod_cast` | `_l_shift_cast` | `_bv_extract` =>
          a

        case BVPred(_) => {
          Console.err.println("Warning: don't know how to handle " + a)
          Incompleteness.set
          a
        }

        case _ =>
          a
      }
    }

    val reducerSettings =
      Param.REDUCER_PLUGIN       .set(
      Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
                                      functionalPredicates),
                                      reducerPlugin)

//    println("after1: " + after1)
    
    val after2 = ReduceWithConjunction(Conjunction.TRUE,
                                       order,
                                       reducerSettings)(after1)

//    println("after2: " + after2)

    after2
  }  

  private object BVPred {
    val reverseMapping =
      (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap
    def unapply(p : Predicate) : Option[IFunction] = reverseMapping get p
  }

  // TODO: add support for all operators

  //////////////////////////////////////////////////////////////////////////////
  //
  //   |EXTRACT| PROPAGATION
  //
  // Extract uses SMT-lib semantics
  // If we have extract(7,3)....
  // What are cut-points.
  // They should represent points in between which we have intervas
  // We should let the first arugment be exclusive
  // e.g., extract(7,3) is cut-point 8 and 3
  // Thus, when looping we get (7,3) and (2,0) in SMT-lib semantics


  // This propagates all cut-points from lhs <-> rhs in extract
  // TODO: Do we need to fix for broken extracts, i.e. extract(1, 1, x, x)...

  private def propagateExtract(extract : (Int, Int, ConstantTerm, ConstantTerm),
                               cutPoints : MMap[Term, Set[Int]]) : Boolean = {
    val (ub, lb, t1, t2) = extract

    var changed = false

    val cut1 = cutPoints.getOrElse(t1, Set())
    val cut2 = cutPoints.getOrElse(t2, Set())

    /// T1 ===> T2
    val t1transformed =
      cut1.map(_ - lb).filter(c => c > 0 && c < (ub - lb + 1))

    if (!(t1transformed subsetOf cut2)) {
      cutPoints += t2 -> (cut2 ++ t1transformed)
      changed = true
    }

    // propagate FROM t2 TO t1
    val t2transformed = cut2.map(_ + lb)

    if (!(t2transformed subsetOf cut1)) {
      cutPoints += t1 -> (cut1 ++ t2transformed)
      changed = true
    }

    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertInt(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-/////////////////////////////////////////////////////////

    changed
  }

  private def propagateDisequality(disequality : (ConstantTerm, ConstantTerm),
                                   cutPoints : MMap[Term, Set[Int]])
                                 : Boolean = {
    val (t1, t2) = disequality
    var changed = false

    val t1cuts = cutPoints.getOrElse(t1, Set())
    val t2cuts = cutPoints.getOrElse(t2, Set())
        
    if (!(t1cuts subsetOf t2cuts)) {
      cutPoints += t2 -> (t2cuts ++ t1cuts)
      changed = true
    }

    if (!(t2cuts subsetOf t1cuts)) {
      cutPoints += t1 -> (t1cuts ++ t2cuts)
      changed = true
    }

    changed
  }

  private def computeCutPoints(extracts : Seq[Atom],
                               disequalities : Seq[LinearCombination])
                             : Map[Term, List[Int]] = {
    val cutPoints = MMap() : MMap[Term, Set[Int]]
    val extractTuples = new ArrayBuffer[(Int, Int, ConstantTerm, ConstantTerm)]
    val diseqTuples = new ArrayBuffer[(ConstantTerm, ConstantTerm)]

    for (Seq(LinearCombination.Constant(IdealInt(ub)),
             LinearCombination.Constant(IdealInt(lb)),
             SingleTerm(t : ConstantTerm),
             res) <- extracts) {
      cutPoints += t -> (Set(lb, ub+1) ++ (cutPoints.getOrElse(t, Set())))
      res match {
        case SingleTerm(s : ConstantTerm) =>
          extractTuples += ((ub, lb, t, s))
        case _ =>
          // nothing
      }
    }

    for (lc <- disequalities)
      if (lc.size == 2 &&
          lc.getCoeff(0) == IdealInt.ONE &&
          lc.getCoeff(1) == IdealInt.MINUS_ONE &&
          lc.constants.size == 2)
        diseqTuples += ((lc.getTerm(0).asInstanceOf[ConstantTerm],
                         lc.getTerm(1).asInstanceOf[ConstantTerm]))

    var changed = true
    while (changed) {
      changed = false
      for (t <- extractTuples) {
        if (propagateExtract(t, cutPoints))
          changed = true
      }

      for (diseq <- diseqTuples) {
        if (propagateDisequality(diseq, cutPoints))
          changed = true
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    cutPoints.map{case (k, v) => k -> v.toList.sorted.reverse}.toMap
  }


  ///////////////////////////
  //
  // EXTRACT (and Diseq) SPLIT FUNCTIONS
  //
  //
  //
  // PRE-CONDITION: parts must have been created using extract (i.e., we can't have
  // extract(1,3) and parts being (0,2) ^ (2,4), but parts should be (0,1) ^ (1,2) ^ (2,3) ^ (3,4)
  private def splitExtract(extract : Atom, cutPoints : List[Int])
                          (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    val Seq(LinearCombination.Constant(IdealInt(upper)),
            LinearCombination.Constant(IdealInt(lower)),
            t1, t2) = extract

    var filterCutPoints = cutPoints.filter(x => x >= lower && x <= upper)

    if (filterCutPoints.length < 2) {
      List()
    } else {
      var curPoint = upper
      var newExtracts = List() : List[Conjunction]

      while (!filterCutPoints.isEmpty) {
        val (ub, lb) = (curPoint, filterCutPoints.head)
        filterCutPoints = filterCutPoints.tail
        curPoint = lb - 1

        val bv1 =
          Atom(_bv_extract,
               List(l(ub),       l(lb),       l(t1), l(v(0))), order)
        val bv2 =
          Atom(_bv_extract,
               List(l(ub-lower), l(lb-lower), l(t2), l(v(0))), order)
        val domain = List(l(v(0)) >= 0, l(v(0)) < pow2(ub-lb+1))
        newExtracts = forall(!conj(bv1 :: bv2 :: domain)) :: newExtracts
      }
      Plugin.RemoveFacts(extract) ::
      (for (c <- newExtracts)
       yield Plugin.AddAxiom(List(extract), !c, ModuloArithmetic.this))
    }
  }

  private def splitDiseq(disequality : LinearCombination,
                         cutPoints : List[Int], goal : Goal)
                        (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    // Make sure c1 != c2 according to cutPoints
    def split(c1 : Term, c2 : Term) : List[Plugin.Action] = {
      val upperBounds : List[IdealInt] = (List(c1,c2).map{
        x => {
          val lc = LinearCombination(IdealInt.MINUS_ONE, x, order)
          goal.facts.arithConj.inEqs.findLowerBound(lc) match {
            case Some(b) => -b
            case None => IdealInt(0)
          }
        }})

      // TODO: Can equality between bit-vectors of diff size be equal?
      val upper = upperBounds.max

      if (upper.signum <= 0)
        return List()

      val bits = upper.getHighestSetBit + 1
      val remCutPoints = for (p <- cutPoints; if 0 < p && p < bits) yield p
      val allPoints = bits :: remCutPoints ::: List(0)

      // We store with upper bound non-exclusive
      var curPoint = allPoints.head - 1
      var iterPoints = allPoints.tail
      var newExtracts = List() : List[Formula]
      var variables = List() : List[(VariableTerm, Int)]

      if (iterPoints.length == 1)
        return List()

      while (!iterPoints.isEmpty) {
        val ub = curPoint
        val lb = iterPoints.head
        iterPoints = iterPoints.tail

        val bitLength = ub - lb + 1
        curPoint = lb - 1

        val (v1, v2) = (v(variables.length), v(variables.length+1))
        variables = (v2, bitLength) :: (v1, bitLength) :: variables
        val (tmp1, tmp2) = (l(v1), l(v2))

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, ub >= 0)
        Debug.assertInt(AC, lb >= 0)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val bv1 = Atom(_bv_extract, List(l(ub), l(lb), l(c1), tmp1), order)
        val bv2 = Atom(_bv_extract, List(l(ub), l(lb), l(c2), tmp2), order)

        val upper = pow2MinusOne(bitLength)
        newExtracts =
          (tmp1 >= 0) :: (tmp1 <= upper) ::
          (tmp2 >= 0) :: (tmp2 <= upper) :: bv1 :: bv2 :: newExtracts
      }

      val diseqs =
        (for (List((v1, bl1), (v2, bl2)) <- variables.sliding(2,2)) yield {
          // TODO: Remove this if domains are not relevant
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, bl1 == bl2)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          v1 === v2
          // conj(v1 >= 0, v1 < pow2(bl1), v2 >= 0, v2 < pow2(bl2), v1 === v2)
        })

      val subFormula = conj(newExtracts) & !conj(diseqs)
      val finalConj = exists(variables.length, subFormula)
      (Plugin.RemoveFacts(disequality =/= 0)) ::
       List(Plugin.AddAxiom(List(disequality =/= 0),
                            finalConj,
                            ModuloArithmetic.this))
    }

    if (cutPoints.isEmpty) {
      List()
    } else if (disequality.constants.size == 1) {
      // -Constant and Integer
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, disequality.leadingCoeff.isOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      split(disequality.leadingTerm, l(-disequality.constant))
    } else if (disequality.constants.size == 2 &&
               disequality.constant.isZero &&
               disequality.getCoeff(0).isOne &&
               disequality.getCoeff(1).isMinusOne) {
      split(disequality.getTerm(0), disequality.getTerm(1))
    } else {
      //println("WARNING: cannot split " + disequality)
      List()
    }
  }

  private def splitExtractActions(extracts : Seq[Atom],
                                  partitions : Map[Term, List[Int]],
                                  goal : Goal)
                                 (implicit order : TermOrder)
                                : Seq[Plugin.Action] =
    for (ex <- extracts;
         action <- ex(2) match {
           case SingleTerm(c : ConstantTerm) =>
             splitExtract(ex, partitions(c))
           case _ =>
             List()
         }) 
    yield action

  /**
   * Splitting of disequalities x != N or x != y
   */
  private def splitDisequalityActions(disequalities : Seq[LinearCombination],
                                      partitions : Map[Term, List[Int]],
                                      goal : Goal)
                                     (implicit order : TermOrder)
                                    : Seq[Plugin.Action] =
    for (diseq <- disequalities;
         lhs = diseq(0)._2;
         parts <- (partitions get lhs).toSeq;
         action <- splitDiseq(diseq, parts, goal))
    yield action

  private def modShiftCast(goal : Goal) : Seq[Plugin.Action] = {
    // check if we have modcast or shiftcast actions
    val actions1 = modCastActions(goal)
    val actions2 = shiftCastActions(goal)

    val resActions1 =
      if (actions1 exists (_.isInstanceOf[Plugin.AxiomSplit]))
        // delayed splitting through a separate task
        List(Plugin.ScheduleTask(ModCastSplitter, 30))
      else
        actions1

    val resActions2 =
      if (actions2 exists (_.isInstanceOf[Plugin.AxiomSplit]))
        // delayed splitting through a separate task
        List(Plugin.ScheduleTask(ShiftCastSplitter, 20))
      else
        actions2

    resActions1 ++ resActions2
  }

  private def elimAtoms(goal : Goal) : Seq[Plugin.Action] = {
    // check whether there are atoms that we can eliminate
    val (castAtoms, (extractConsts, extractAtoms, extractDefs)) =
      eliminatableAtoms(goal)

    val castActions =
      if (!castAtoms.isEmpty) {
        val elimConsts =
          (for (a <- castAtoms; c <- a.last.constants) yield c).toSet
        val elimInEqs =
          InEqConj(
            for (lc <- goal.facts.arithConj.inEqs.iterator;
              if !Seqs.disjoint(elimConsts, lc.constants))
            yield lc,
            goal.order)
        val elimFormulas =
          Conjunction.conj(castAtoms ++ List(elimInEqs), goal.order)

        List(Plugin.RemoveFacts(elimFormulas),
          Plugin.AddReducableModelElement(elimFormulas, elimConsts,
            goal.reducerSettings))
      } else {
        List()
      }

    val extractActions =
      if (!extractConsts.isEmpty) {
        val elimInEqs =
          InEqConj(
            for (lc <- goal.facts.arithConj.inEqs.iterator;
              if !Seqs.disjoint(extractConsts, lc.constants))
            yield lc,
            goal.order)
        val elimFormulas =
          Conjunction.conj(extractAtoms ++ List(elimInEqs), goal.order)
        val allExtractDefs =
          Conjunction.conj(List(extractDefs, elimInEqs), goal.order)

        List(Plugin.RemoveFacts(elimFormulas),
          Plugin.AddReducableModelElement(allExtractDefs, extractConsts,
            goal.reducerSettings))
      } else {
        List()
      }

    castActions ++ extractActions
  }

  /**
   * Replace negated predicates with positive predicates
   */
  private def negPreds(goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val negPreds1 =
      goal.facts.predConj.negativeLitsWithPred(_mod_cast) ++
      goal.facts.predConj.negativeLitsWithPred(_l_shift_cast)

    val actions1 =
      if (!negPreds1.isEmpty) {
        (for (a <- negPreds1) yield {
          val axiom =
            exists(Atom(a.pred, a.init ++ List(l(v(0))), order) &
              (v(0) >= a(0)) & (v(0) <= a(1)) & (v(0) =/= a.last))
          Plugin.AddAxiom(List(!conj(a)), axiom, ModuloArithmetic.this)
        }) ++ List(Plugin.RemoveFacts(conj(
                            for (a <- negPreds1) yield !conj(a))))
      } else {
        List()
      }

    val negPreds2 =
      for (a <- goal.facts.predConj.negativeLitsWithPred(_bv_extract);
           // negative predicates can be handled only if bit arguments
           // are concrete (would need exponentiation function otherwise)
           if a(0).isConstant && a(1).isConstant)
      yield a

    val actions2 =
      if (!negPreds2.isEmpty) {
        (for (a <- negPreds2) yield {
          val sort@ModSort(sortLB, sortUB) =
            (SortedPredicate argumentSorts a).last
          val axiom =
            exists(Atom(a.pred, a.init ++ List(l(v(0))), order) &
              (v(0) >= sortLB) & (v(0) <= sortUB) & (v(0) =/= a.last))
          Plugin.AddAxiom(List(!conj(a)), axiom, ModuloArithmetic.this)
        }) ++ List(Plugin.RemoveFacts(conj(
                            for (a <- negPreds2) yield !conj(a))))
      } else {
        List()
      }

    actions1 ++ actions2
  }

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def printBVgoal(goal : Goal) = {
    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
    val diseqs = goal.facts.arithConj.negativeEqs

    println("HandleGoal")
    // println(goal)
    if (!goal.facts.predConj.positiveLits.filterNot(_.pred.name == "bv_extract").isEmpty) {
      println("+--------------------------PREDCONJ----------------------+")
      for (f <- goal.facts.predConj.positiveLits.filterNot(_.pred.name == "bv_extract"))
        println("|\t" + f)
    }

    if (!extracts.isEmpty) {
      println("+--------------------BVEXTRACTS--------------------------+")
      for (ex <- extracts) {
        println("|\t" + ex)
      }
    }

    if (!diseqs.isEmpty) {
      println("+----------------------DISEQS---------------------------+")
      for (diseq <- diseqs) {
        println("|\t" + diseq)
      }
    }
     {
      println("+----------------------INEQS---------------------------+")
      for (ie <- goal.facts.arithConj.inEqs) {
        println("|\t" + ie + " >= 0")
      }
    }
    println("+-------------------------------------------------------+")
  }
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  override val dependencies : Iterable[Theory] = List(MultTheory)

  def plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      implicit val _ = goal.order
      import TerForConvenience._

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug)
        printBVgoal(goal)
     //-END-ASSERTION-//////////////////////////////////////////////////////////

      val negPs = negPreds(goal)
      if (!negPs.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Negative predicate actions:")
          for (a <- negPs)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return negPs
      }

      val elimActions = elimAtoms(goal)
      if (!elimActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Eliminatable atoms actions:")
          for (a <- elimActions)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return elimActions
      }

      // extract-predicates in the goal

      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
      val extractedConsts =
        (for (Seq(_, _, SingleTerm(c : ConstantTerm), _) <- extracts.iterator)
         yield c).toSet

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      for (ex <- extracts) {
        Debug.assertInt(AC,
          ex(0).asInstanceOf[LinearCombination0].constant.signum >= 0 &&
          ex(1).asInstanceOf[LinearCombination0].constant.signum >= 0)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val diseqs = for (lc <- goal.facts.arithConj.negativeEqs;
                        if !Seqs.disjoint(lc.constants, extractedConsts))
                   yield lc
      val partitions = computeCutPoints(extracts, diseqs)

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug && !partitions.isEmpty) {
        println("<<Partitions>>")
        for ((k, v) <- partitions){
          println("\t" + k + " --> " + v)
        }
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      // Let's start by only splitting one variable
      val splitActions = splitExtractActions(extracts, partitions, goal)

      if (!splitActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Splitting extracts")
          for (t <- splitActions)
            println("\t" + t)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return splitActions
      }

      var actions = new ArrayBuffer[Plugin.Action]

      if (!extracts.isEmpty) {
        // If necessary, turn extracts in arithmetic context into
        // just arithmetic constaints
        actions += Plugin.ScheduleTask(ExtractArithEncoder, 10)
      }

      val diseqActions = splitDisequalityActions(diseqs, partitions, goal) /* ++
                         splitDisInequalityActions(pureExtractedConsts,
                                                   partitions,
                                                   goal) ++
                         splitDisInequalityActions2(pureExtractedConsts,
                                                    partitions,
                                                    goal) */
      if (!diseqActions.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Splitting disequalities actions:")
          for (t <- diseqActions)
            println("\t" + t)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return actions ++ diseqActions
      }

      val msc = modShiftCast(goal)
      if (!msc.isEmpty) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        if (debug) {
          println("Mod Shift Casting:")
          for (a <- msc)
            println("\t" + a)
        }
        //-END-ASSERTION-///////////////////////////////////////////////////////
        return actions ++ msc
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug)
        println("Nothing..")
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions
    }
  })

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find positive atoms in the goal that can be eliminated.
   */
  private def eliminatableAtoms(goal : Goal)
                  : (Seq[Atom],                     // cast lits
                     (Set[ConstantTerm], Seq[Atom], // extract lits
                      Conjunction)) = {
    val eliminatedIsolatedConstants = goal.eliminatedIsolatedConstants

    if (eliminatedIsolatedConstants.isEmpty)
      return (List(), (Set(), List(), Conjunction.TRUE))

    val facts = goal.facts

    val predConj = facts.predConj
    val castLits = predConj.positiveLitsWithPred(_mod_cast) ++
                   predConj.positiveLitsWithPred(_l_shift_cast)
    val extractLits = predConj.positiveLitsWithPred(_bv_extract)

    if (castLits.isEmpty && extractLits.isEmpty)
      return (List(), (Set(), List(), Conjunction.TRUE))

    val inEqs = facts.arithConj.inEqs

    // find constants that can be eliminated

    val constOccurs, unelimConsts = new MHashSet[ConstantTerm]
    unelimConsts ++= facts.arithConj.positiveEqs.constants
    unelimConsts ++= facts.arithConj.negativeEqs.constants
    unelimConsts ++= (for (a <- predConj.negativeLits.iterator;
                           c <- a.constants.iterator) yield c)
    unelimConsts ++= (for (lc <- inEqs.iterator;
                           if lc.constants.size >= 2;
                           c <- lc.constants.iterator) yield c)

    val lastLB = new MHashMap[ConstantTerm, Int]
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    val lastUB = new MHashMap[ConstantTerm, Int]
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    for (a <- predConj.positiveLits) a match {
      case Atom(`_bv_extract`,
                Seq(LinearCombination.Constant(IdealInt(ub)),
                    LinearCombination.Constant(IdealInt(lb)),
                    SingleTerm(c : ConstantTerm),
                    res),
                _)
          if !(unelimConsts contains c) &&
             ((lastLB get c) match {
               case Some(oldLB) =>
                 oldLB > ub
               case None =>
                 // if we haven't seen this constant in
                 // an extract literal yet, we must not have
                 // seen it at all
                 !(constOccurs contains c) &&
                 hasImpliedIneqConstraints(c, IdealInt.ZERO,
                                           pow2MinusOne(ub + 1), inEqs)
             }) => {
        constOccurs add c
        lastLB.put(c, lb)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        // we rely on the fact that the extract literals are sorted
        // in decreasing order
        Debug.assertInt(AC, ub <= lastUB.getOrElse(c, Int.MaxValue))
        lastUB.put(c, ub)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        unelimConsts ++= res.constants
      }
      case Atom(`_bv_extract`, _, _) =>
        for (lc <- a.iterator; c <- lc.constants.iterator)
          unelimConsts add c
      case a =>
        for (lc <- a.iterator; c <- lc.constants.iterator)
          if (!(constOccurs add c))
            unelimConsts add c
    }

    // find cast atoms with those constants

    val castElims =
      for (a@Atom(_,
                  Seq(LinearCombination.Constant(lower),
                      LinearCombination.Constant(upper),
                      _*),
                  _) <- castLits;
           SingleTerm(resConst : ConstantTerm) <- List(a.last);
           if (eliminatedIsolatedConstants contains resConst) &&
               !(unelimConsts contains resConst) &&
               hasImpliedIneqConstraints(resConst, lower, upper, inEqs))
      yield a

    // find extract atoms with those constants

    val backTranslation =
      new MHashMap[ConstantTerm, ArrayBuffer[(IdealInt, LinearCombination)]]

    val extractElims =
      for (a@Atom(_,
                  Seq(_,
                      LinearCombination.Constant(lb),
                      SingleTerm(c : ConstantTerm),
                      res),
                  _) <- extractLits;
           if (eliminatedIsolatedConstants contains c) &&
               !(unelimConsts contains c)) yield {
        backTranslation.getOrElseUpdate(c, new ArrayBuffer) += ((pow2(lb), res))
        a
      }

    implicit val order = goal.order
    import TerForConvenience._

    val extractDefs : Conjunction =
      eqZ(for ((c, parts) <- backTranslation) yield {
            parts += ((IdealInt.MINUS_ONE, LinearCombination(c, order)))
            LinearCombination.sum(parts, order)
          })

    (castElims, (backTranslation.keySet.toSet, extractElims, extractDefs))
  }

  private def hasImpliedIneqConstraints(c : ConstantTerm,
                                        lower : IdealInt,
                                        upper : IdealInt,
                                        ineqs : InEqConj) : Boolean =
      ineqs forall { lc =>
        !(lc.constants contains c) ||
        (lc.constants.size == 1 &&
         (lc.leadingCoeff match {
            case IdealInt.ONE       => -lc.constant <= lower
            case IdealInt.MINUS_ONE => lc.constant >= upper
            case _                  => false
          }))
      }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Splitter handles the splitting of mod_cast-operations, when no other
   * inference steps are possible anymore.
   */
  private object ModCastSplitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
//println("mod splitter " + goal.facts)
      modCastActions(goal)
    }
  }

  /**
   * Splitter handles the splitting of mod_cast-operations, when no other
   * inference steps are possible anymore.
   */
  private object ShiftCastSplitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
//println("shift splitter " + goal.facts)
      shiftCastActions(goal)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * ExtractArithEncoder translates bv_extract to an existentially quantified
   * equation
   */
  private object ExtractArithEncoder extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
      import TerForConvenience._
      implicit val order = goal.order

      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)
      val inEqs = goal.facts.arithConj.inEqs

      if (extracts.isEmpty)
        return List()

      val terms =
        new LinkedHashMap[LinearCombination,
                          (Int, Int, List[(IdealInt, Term)],
                           Int, List[LinearCombination],
                           List[Atom])]

      def elimExtract(ex : Atom,
                      ub : Int, lb : Int,
                      arg : LinearCombination,
                      res : LinearCombination) : Unit = {
        (terms get arg) match {
          case None =>
            terms.put(arg, (ub, lb, List((pow2(lb), res)), 0, List(), List(ex)))
          case Some((firstUB, lastLB, ts, nextVarInd, constraints, atoms)) =>
            if (lastLB > ub + 1) {
              // need to put a quantified variable in between
              val vv = v(nextVarInd)
              val newTS = (pow2(lb), res) :: (pow2(ub + 1), vv) :: ts
              val newConstraints =
                (pow2MinusOne(lastLB - ub - 1) - l(vv)) ::
                (l(vv)) :: constraints
              terms.put(arg, (firstUB, lb, newTS,
                              nextVarInd+1, newConstraints, ex :: atoms))
            } else if (lastLB == ub + 1) {
              // no variable needed
              terms.put(arg, (firstUB, lb, (pow2(lb), res) :: ts,
                              nextVarInd, constraints, ex :: atoms))
            } else {
              // nothing; this extract cannot be eliminated, since it
              // overlaps with the last one
            }
        }
      }

      val arithExtractedConsts = new MHashSet[ConstantTerm]
      arithExtractedConsts ++= arithmeticExtractedConsts(goal)

      for (ex <- extracts) ex match {
        case Atom(`_bv_extract`,
                  Seq(LinearCombination.Constant(IdealInt(ub)),
                      LinearCombination.Constant(IdealInt(lb)),
                      arg@SingleTerm(c : ConstantTerm),
                      res),
                  _) =>
          if ((arithExtractedConsts contains c) ||
              !hasImpliedIneqConstraints(c, IdealInt.ZERO,
                                         pow2MinusOne(ub + 1), inEqs)) {
            arithExtractedConsts += c
            elimExtract(ex, ub, lb, arg, res)
          }
        case Atom(`_bv_extract`,
                  Seq(LinearCombination.Constant(IdealInt(ub)),
                      LinearCombination.Constant(IdealInt(lb)),
                      arg,
                      res),
                  _) =>
          elimExtract(ex, ub, lb, arg, res)
        case _ =>
          // nothing
      }

      if (terms.isEmpty)
        return List()

      // if necessary, add a variable for the least-significant bits
      for (arg <- terms.keys) terms(arg) match {
        case (_, 0, _, _, _, _) =>
          // nothing
        case (_, lastUB, _, _, _, atoms) =>
          elimExtract(atoms.head, -1, 0, arg, l(0))
      }

      val axioms =
        for ((arg, (firstUB, lastLB, ts, varNum,
                    constraints, atoms)) <- terms) yield {
          val modRes = LinearCombination(ts, order)
          val defFor =
            exists(varNum,
                   conj(constraints >= 0,
                        _mod_cast(List(l(0), l(pow2MinusOne(firstUB+1)),
                                       l(arg), modRes))))
          Plugin.AddAxiom(atoms.distinct, defFor, ModuloArithmetic.this)
        }

      val toRemove =
        conj(for (Plugin.AddAxiom(atoms, _, _) <- axioms.iterator;
                  a <- atoms.iterator)
             yield a)

      val actions = List(Plugin.RemoveFacts(toRemove)) ++ axioms

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      if (debug) {
        println("Extract to arithmetic:")
        for (a <- actions)
          println("\t" + a)
      }
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      actions
    }

    /**
     * Determine constants that occur in general arithmetic context.
     */
    private def arithmeticExtractedConsts(goal : Goal)
                                        : MHashSet[ConstantTerm] = {
      val arithConsts = new MHashSet[ConstantTerm]

      val facts = goal.facts
      val ac = facts.arithConj

      arithConsts ++= ac.positiveEqs.constants

      for (lc <- ac.inEqs)
        if (lc.constants.size > 1)
          arithConsts ++= lc.constants

      for (a <- facts.predConj.positiveLits) a match {
        case Atom(`_bv_extract`,
                  Seq(_, _, SingleTerm(_), _), _) =>
          // nothing
        case Atom(`_bv_extract`,
                  Seq(_,  _, arg, _), _) =>
          arithConsts ++= arg.constants
        case a =>
          arithConsts ++= a.constants
      }

      for (a <- facts.predConj.negativeLits)
        arithConsts ++= a.constants

      arithConsts
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def shiftCastActions(goal : Goal) : Seq[Plugin.Action] =  {
    val castPreds =
      goal.facts.predConj.positiveLitsWithPred(_l_shift_cast).toBuffer

    Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

    val reducer = goal.reduceWithFacts
    implicit val order = goal.order
    import TerForConvenience._

    // find simple l_shift_cast predicates that can be replaced by mod_cast
    var simpleElims : List[Plugin.Action] = List()
    
    var bestSplitNum = Int.MaxValue
    var splitPred : Option[(Atom,
                            IdealInt,  // lower exponent bound
                            IdealInt,  // upper exponent bound
                            Boolean,   // for upper bound all bits after shift
                                       // are zero
                            List[Formula])] = None

    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

    for (a <- castPreds) {
      var assumptions : List[Formula] = List(a)

      def addInEqAssumption(ineqs : Seq[LinearCombination]) =
        for (lc <- ineqs)
          assumptions = InEqConj(lc, order) :: assumptions

      if (a(2).isZero) {

        simpleElims =
          Plugin.RemoveFacts(a) ::
          Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order),
                          ModuloArithmetic.this) ::
          simpleElims

      } else if (a(3).isConstant) {

        simpleElims =
          Plugin.RemoveFacts(a) ::
          Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                            Array(a(0), a(1),
                                  a(2) * pow2(a(3).constant max IdealInt.ZERO),
                                  a(4)),
                            order),
                          ModuloArithmetic.this) ::
          simpleElims

      } else {

        val modulus = getModulus(a)
        val pow2Modulus = (modulus & (modulus - 1)).isZero

        val lBound =
          if (proofs)
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(3)) yield {
              // only non-negative bounds matter at this point!
              if (b.signum >= 0)
                addInEqAssumption(assum)
              b
            }
          else
            reducer lowerBound a(3)

        val (uBound, vanishing) =
          (reducer upperBound a(3)) match {
            case Some(ub)
              if (!pow2Modulus || ub < IdealInt(modulus.getHighestSetBit)) =>
                if (proofs) {
                  val Some((b, assum)) = reducer upperBoundWithAssumptions a(3)
                  addInEqAssumption(assum)
                  (Some(b), false)
                } else {
                  (Some(ub), false)
                }
            case _ if pow2Modulus =>
              (Some(IdealInt(modulus.getHighestSetBit)), true)
            case _ =>
              (None, false)
          }

        (lBound, uBound) match {
          case (_, Some(upper)) if upper.signum <= 0 => {
            simpleElims =
              Plugin.RemoveFacts(a) ::
              Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                               Array(a(0), a(1), a(2), a(4)),
                               order),
                          ModuloArithmetic.this) ::
              simpleElims
          }
          case (Some(lower), Some(upper)) if lower >= upper => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, vanishing)
            //-END-ASSERTION-///////////////////////////////////////////////////

            // TRANSLATE TO BV_EXTRACT
            simpleElims =
              Plugin.RemoveFacts(a) ::
              Plugin.AddAxiom(assumptions,
                          Atom(_mod_cast,
                               Array(a(0), a(1),
                                     LinearCombination.ZERO, a(4)),
                               order),
                          ModuloArithmetic.this) ::
              simpleElims
          }
          case (rawLower, Some(upper)) if simpleElims.isEmpty => {
            // need to do some splitting
            val lower = rawLower getOrElse IdealInt.MINUS_ONE
            val cases = (upper - (lower max IdealInt.ZERO) + 1).intValueSafe
            if (cases < bestSplitNum) {
              bestSplitNum = cases
              splitPred = Some((a, lower, upper, vanishing, assumptions))
            }
          }
          case _ =>
            // nothing
        }

      }
    }

    if (!simpleElims.isEmpty) {

      simpleElims

    } else if (splitPred.isDefined) {

      val Some((a, lower, upper, vanishing, assumptions)) = splitPred

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, lower < upper && upper.signum >= 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val cases =
        (for (n <- IdealRange(lower max IdealInt.ZERO, upper + 1)) yield {
           if (n.isZero && lower < n) {
             (conj(List(a(3) <= n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), a(2), a(4)),
                             order))),
              List())
           } else if (vanishing && n == upper) {
             (conj(List(a(3) >= n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), LinearCombination.ZERO, a(4)),
                             order))),
              List())
           } else {
             (conj(List(a(3) === n,
                        Atom(_mod_cast,
                             Array(a(0), a(1), a(2) * pow2(n), a(4)),
                             order))),
              List())
           }
         }).toBuffer

      List(Plugin.RemoveFacts(a),
           Plugin.AxiomSplit(assumptions,
                             cases.toList,
                             ModuloArithmetic.this))

    } else {

      List()

    }
  }

  //////////////////////////////////////////////////////////////////////////////

  // TODO: backward propagation for the mod_cast function

  private val SPLIT_LIMIT = IdealInt(20)

    private def modCastActions(goal : Goal) : Seq[Plugin.Action] =  {
      val castPreds =
        goal.facts.predConj.positiveLitsWithPred(_mod_cast).toBuffer
      // TODO: handle occurring _mul predicates in a special way?

      Param.RANDOM_DATA_SOURCE(goal.settings).shuffle(castPreds)

      val reducer = goal.reduceWithFacts
      implicit val order = goal.order
      import TerForConvenience._

      // find simple mod_cast predicates that can be replaced by equations
      var simpleElims : List[Plugin.Action] = List()

      // find a mod_cast predicate that can be split into a small number of
      // cases
      var bestSplitNum = SPLIT_LIMIT
      var bestSplitPred : Option[(Atom,
                                  IdealInt, // lowerFactor
                                  IdealInt, // upperFactor
                                  IdealInt, // wastedLower
                                  IdealInt, // wastedUpper
                                  List[Formula], ModSort)] = None

      // find a predicate that has to be eliminated through a quantifier
      var someQuantPred : Option[Atom] = None

      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      for (a <- castPreds) {
        var assumptions : List[Formula] = List(a)

        def addInEqAssumption(ineqs : Seq[LinearCombination]) =
          for (lc <- ineqs)
            assumptions = InEqConj(lc, order) :: assumptions

        val lBound =
          if (proofs)
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(2)) yield {
              addInEqAssumption(assum)
              b
            }
          else
            reducer lowerBound a(2)

        val uBound =
          if (lBound.isDefined) {
            if (proofs)
              for ((b, assum) <- reducer upperBoundWithAssumptions a(2)) yield {
                addInEqAssumption(assum)
                b
              }
            else
              reducer upperBound a(2)
          } else {
            None
          }

        (lBound, uBound) match {
          case (Some(lb), Some(ub)) => {
            val sort@ModSort(sortLB, sortUB) =
              (SortedPredicate argumentSorts a).last

            val lowerFactor = (lb - sortLB) / sort.modulus
            val upperFactor = -((sortUB - ub) / sort.modulus)

            if (lowerFactor == upperFactor) {
              // in this case, no splitting is necessary

              simpleElims =
                Plugin.RemoveFacts(a) ::
                Plugin.AddAxiom(
                       assumptions,
                       a(2) === a(3) + (lowerFactor * sort.modulus),
                       ModuloArithmetic.this) :: simpleElims
                       
            } else if (simpleElims.isEmpty) {
            
              val caseNum = upperFactor - lowerFactor + 1

              if (someQuantPred.isEmpty && caseNum >= SPLIT_LIMIT) {
                someQuantPred =
                  Some(a)
              } else if (caseNum < bestSplitNum) {
                bestSplitNum =
                  caseNum
                val wastedLower =
                  lb - (lowerFactor * sort.modulus + sortLB)
                val wastedUpper =
                  (upperFactor * sort.modulus + sortUB) - ub
                bestSplitPred =
                  Some((a, lowerFactor, upperFactor,
                        wastedLower, wastedUpper, assumptions, sort))
              }
            }
          }

          case _ =>
            someQuantPred = Some(a)
        }
      }

      if (!simpleElims.isEmpty) {

        simpleElims

      } else if (bestSplitPred.isDefined) {

        val Some((a, lowerFactor, upperFactor,
                  wastedLower, wastedUpper, assumptions, sort)) =
          bestSplitPred

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, lowerFactor < upperFactor)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val cases =
          (for (n <-
                  // consider the inner cases first
                  IdealRange(lowerFactor + 1, upperFactor).iterator ++
                  (if (wastedLower < wastedUpper)
                     Seqs.doubleIterator(lowerFactor, upperFactor)
                   else
                     Seqs.doubleIterator(upperFactor, lowerFactor));
                f = conj(a(2) === a(3) + (n * sort.modulus));
                if !f.isFalse)
           yield (f, List())).toBuffer

        List(Plugin.RemoveFacts(a),
             Plugin.AxiomSplit(assumptions,
                               cases.toList,
                               ModuloArithmetic.this))
        
      } else if (someQuantPred.isDefined) {

        val Some(a) =
          someQuantPred
        val sort =
          (SortedPredicate argumentSorts a).last.asInstanceOf[ModSort]

        List(Plugin.RemoveFacts(a),
             Plugin.AddAxiom(List(a),
                             exists(a(2) === a(3) + (v(0) * sort.modulus)),
                             ModuloArithmetic.this))

      } else {

        List()

      }
    }


  //////////////////////////////////////////////////////////////////////////////

  private def getLeadingTerm(a : Atom, order : TermOrder) : Term = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, a.pred == _mod_cast && !a(2).isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val lt1 = a(2).leadingTerm
    if (a(3).isConstant) {
      lt1
    } else {
      val lt2 = a(3).leadingTerm
      if (order.compare(lt1, lt2) > 0)
        lt1
      else
        lt2
    }
  }

  /**
   * Compute the effective leading coefficient of the modulo atom <code>a</code>
   * for simplifying modulo the given <code>modulus</code>.
   */
  private def effectiveLeadingCoeff(a : Atom,
                                    modulus : IdealInt,
                                    order : TermOrder) : IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, a.pred == _mod_cast && !a(2).isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val aModulus = getModulus(a)
    val modulusLCM = aModulus lcm modulus

    val leadingCoeff =
      if (a(3).isConstant ||
          order.compare(a(2).leadingTerm, a(3).leadingTerm) > 0)
        a(2).leadingCoeff
      else
        a(3).leadingCoeff

    leadingCoeff * (modulusLCM / aModulus)
  }

  private def getModulus(a : Atom) : IdealInt = {
    val (lower, upper) = getLowerUpper(a)
    upper - lower + 1
  }

  private def atomsContainVariables(atoms : Seq[Atom]) : Boolean =
    atoms exists { a => !a.variables.isEmpty }

  // TODO: this is quite slow?
  private def extractModulos(atoms : Seq[Atom], order : TermOrder)
                            (t : Term) : Iterator[Atom] =
    for (a <- atoms.iterator;
         if a.pred == _mod_cast &&
            // avoid cyclic rewriting
            !a(2).isConstant &&
            (a(3).isConstant || a(2).leadingTerm != a(3).leadingTerm);
         if getLeadingTerm(a, order) == t)
    yield a

  private val emptyIteratorFun = (t : Term) => Iterator.empty

  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val atoms = conj.predConj.positiveLitsWithPred(_mod_cast)
      new Reducer(if (atoms.isEmpty)
                    emptyIteratorFun
                  else
                    extractModulos(atoms, order) _,
                  atomsContainVariables(atoms),
                  order)
    }
  }

  class Reducer(modulos : Term => Iterator[Atom],
                containsVariables : Boolean,
                order : TermOrder) extends ReducerPlugin {
    val factory = ReducerFactory
    
    def passQuantifiers(num : Int) =
      if (containsVariables && num > 0) {
        val downShifter = VariableShiftSubst.downShifter[Term](num, order)
        val upShifter =   VariableShiftSubst.upShifter[Atom](num, order)
        new Reducer((t:Term) =>
                    if (downShifter isDefinedAt t)
                      for (a <- modulos(downShifter(t))) yield upShifter(a)
                    else
                      Iterator.empty,
                    true,
                    order)
      } else {
        this
      }

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = mode match {
      case ReducerPlugin.ReductionMode.Contextual => {
        val newAtoms = predConj.positiveLitsWithPred(_mod_cast)
        if (newAtoms.isEmpty)
          this
        else
          new Reducer((t:Term) =>
                        extractModulos(newAtoms, order)(t) ++ modulos(t),
                      containsVariables || atomsContainVariables(newAtoms),
                      order)
      }
      case ReducerPlugin.ReductionMode.Simple =>
        this
    }

    def reduce(predConj : PredConj,
               reducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult =
      {
        Timeout.check
        val logging = logger.isLogging

        implicit val order = predConj.order
        import TerForConvenience._

        // TODO: eliminate mod_cast arguments with large coefficients

        {
          // Cache for uniquely defined bits of given lcs
          val bitCache = new LRUCache[LinearCombination,
                                      (Int, IdealInt, Seq[Formula])](32)

          // First eliminate some atoms that can be evaluated
          ReducerPlugin.rewritePreds(predConj,
                                     List(_mod_cast, _l_shift_cast,
                                          _bv_extract),
                                     order,
                                     logger) { a =>
              a.pred match {
                case `_mod_cast` =>
                  (reducer.lowerBound(a(2), logging),
                   reducer.upperBound(a(2), logging)) match {
          
                    case (Some((lb, lbAsses)), Some((ub, ubAsses))) => {
                      val sort@ModSort(sortLB, sortUB) =
                        (SortedPredicate argumentSorts a).last
                
                      val lowerFactor = (lb - sortLB) / sort.modulus
                      val upperFactor = -((sortUB - ub) / sort.modulus)

                      if (lowerFactor == upperFactor) {
                        val newEq = a(2) === a(3) + (lowerFactor * sort.modulus)
                        logger.otherComputation(lbAsses ++ ubAsses ++ List(a),
                                                newEq, order,
                                                ModuloArithmetic.this)
                        newEq
                      } else {
                        a
                      }
                    }
            
                    case _ =>
                      a
                  }

                case `_l_shift_cast` =>
                  if (a(2).isZero) {
                    val newA =
                      Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order)
                    logger.otherComputation(List(a), newA, order,
                                            ModuloArithmetic.this)
                    newA
                  } else if (a(3).isConstant) {
                    val sort@ModSort(_, _) =
                      (SortedPredicate argumentSorts a).last
                    val newA =
                      Atom(_mod_cast,
                           Array(a(0), a(1),
                                 a(2) *
                                   pow2Mod(a(3).constant max IdealInt.ZERO,
                                           sort.modulus),
                                 a(4)),
                           order)
                    logger.otherComputation(List(a), newA, order,
                                            ModuloArithmetic.this)
                    newA
                  } else {
                    (reducer.lowerBound(a(3), logging)) match {
                      case Some((lb, lbAsses)) if lb.signum > 0 => {
                        val sort@ModSort(_, _) =
                          (SortedPredicate argumentSorts a).last
                        val newA = Atom(_l_shift_cast,
                                        Array(a(0), a(1),
                                              a(2) * pow2Mod(lb, sort.modulus),
                                              a(3) - lb, a(4)),
                                        order)
                        logger.otherComputation(lbAsses ++ List(a), newA, order,
                                                ModuloArithmetic.this)
                        newA
                      }
                      case _ =>
                        a
                    }
                  }

                case `_bv_extract` =>
                  if (a(2).isConstant) {
                    val LinearCombination.Constant(IdealInt(ub)) = a(0)
                    val LinearCombination.Constant(IdealInt(lb)) = a(1)

                    val newEq = a(3) === evalExtract(ub, lb, a(2).constant)

                    //-BEGIN-ASSERTION-/////////////////////////////////////////
                    if (debug) {
                      println("Evaluating bv_extract:")
                      println("\t" + a)
                      println("\t" + newEq)
                    }
                    //-END-ASSERTION-///////////////////////////////////////////

                    logger.otherComputation(List(a), newEq, order,
                                            ModuloArithmetic.this)
                    newEq
                  } else {
                    val (bitBoundary, lower, asses) = bitCache(a(2)) {
                      (reducer.lowerBound(a(2), logging),
                       reducer.upperBound(a(2), logging)) match {
                        case (Some((lb, lbA)),
                              Some((ub, ubA))) if lb.signum >= 0 =>
                          ((lb ^ ub).getHighestSetBit + 1, lb, lbA ++ ubA)
                        case _ =>
                          (-1, IdealInt.ZERO, List())
                      }
                    }

                    if (bitBoundary >= 0) {
                      val LinearCombination.Constant(IdealInt(lb)) = a(1)
                      if (lb >= bitBoundary) {
                        val LinearCombination.Constant(IdealInt(ub)) = a(0)
                        val newEq = a(3) === evalExtract(ub, lb, lower)

                        //-BEGIN-ASSERTION-/////////////////////////////////////
                        if (debug) {
                          println("Evaluating bv_extract:")
                          println("\t" + a)
                          println("\t" + newEq)
                        }
                        //-END-ASSERTION-///////////////////////////////////////

                        logger.otherComputation(List(a) ++ asses, newEq, order,
                                                ModuloArithmetic.this)
                        newEq
                      } else {
                        a
                      }
                    } else {
                      a
                    }
                  }
              }
          
        }} orElse {
          // then try to rewrite modulo atoms using known facts

          var rewritten : List[Atom] = List()
          val additionalAtoms = predConj.positiveLitsWithPred(_mod_cast)
          
          def getModulos(t : Term) = mode match {
            case ReducerPlugin.ReductionMode.Contextual =>
              modulos(t) ++ (
                for (a <- extractModulos(additionalAtoms, order)(t);
                     if !(rewritten contains a))
                yield a
              )
            case ReducerPlugin.ReductionMode.Simple =>
              modulos(t)
          }

          ReducerPlugin.rewritePreds(predConj,
                                     List(_mod_cast, _l_shift_cast),
                                     order,
                                     logger) {
            a => {
              lazy val modulus = getModulus(a)
              
              val simplifiers =
                for ((coeff, t) <- a(2).iterator;
                     knownAtom <- getModulos(t);
                     if knownAtom != a;
                     simpCoeff = effectiveLeadingCoeff(knownAtom, modulus,
                                                       order);
                     reduceMult = (coeff reduceAbs simpCoeff)._1;
                     if !reduceMult.isZero)
                yield (knownAtom, reduceMult * simpCoeff)

              if (simplifiers.hasNext) {
                val (knownAtom, subtractedValue) = simplifiers.next

                val lc = knownAtom(2) - knownAtom(3)
                val newA2 = LinearCombination.sum(
                              Array((IdealInt.ONE, a(2)),
                                    (-(subtractedValue / lc.leadingCoeff), lc)),
                              order)
                val newA = Atom(a.pred, a.updated(2, newA2), order)
//                println("simp: " + a + " -> " + newA)

                logger.otherComputation(List(knownAtom, a), newA, order,
                                        ModuloArithmetic.this)

                rewritten = a :: rewritten

                newA
              } else {
                a
              }
            }
          }
        }
      }

    /**
     * Perform GC, remove literals that are no longer needed in a formula.
     */
    def finalReduce(conj : Conjunction) =
      if (conj.quans.isEmpty) {
        conj
      } else if (conj.isQuantifiedNegatedConjunction) {
        val subConj =
          conj.negatedConjs.head
        val newSubConj =
          finalReduceHelp(subConj, for (q <- conj.quans) yield q.dual)

        if (subConj eq newSubConj) {
          conj
        } else {
          implicit val order = conj.order
          conj.updateNegatedConjs(NegatedConjunctions(newSubConj, order))
        }
      } else {
        finalReduceHelp(conj, conj.quans)
      }

    private def finalReduceHelp(conj : Conjunction,
                                quans : Seq[Quantifier]) : Conjunction = {
      if (!(quans contains Quantifier.EX))
        return conj

      val predConj = conj.predConj
      val quanNum = quans.size
      val castLits = predConj.positiveLitsWithPred(_mod_cast)

      if (castLits.isEmpty)
        return conj

      // check which of the casts have results in terms of existentially
      // quantified variables
      val varLits =
        for (a@Atom(_,
                    Seq(LinearCombination.Constant(lower),
                        LinearCombination.Constant(upper),
                        _,
                        SingleTerm(resVar : VariableTerm)),
                    _) <- castLits;
             if resVar.index < quanNum &&
                quans(resVar.index) == Quantifier.EX &&
                hasImpliedIneqConstraints(resVar, lower, upper,
                                          conj.arithConj.inEqs))
        yield a

      if (varLits.isEmpty)
        return conj

      // check which of the result variables are not used anywhere else

      val varOccurs, unelimVars = new MHashSet[VariableTerm]
      unelimVars ++= conj.arithConj.positiveEqs.variables
      unelimVars ++= conj.arithConj.negativeEqs.variables
      unelimVars ++= (for (a <- predConj.negativeLits.iterator;
                           v <- a.variables.iterator) yield v)
      unelimVars ++= conj.negatedConjs.variables

      for (a <- predConj.positiveLits.iterator;
           lc <- a.iterator;
           v <- lc.variables.iterator)
        if (!(varOccurs add v))
          unelimVars add v

      val elimLits =
        (for (a@Atom(_,
                     Seq(_, _, _, SingleTerm(resVar : VariableTerm)),
                     _) <- varLits.iterator;
              if !(unelimVars contains resVar))
         yield a).toSet

      if (elimLits.isEmpty)
        return conj

      val newPosLits =
        predConj.positiveLits filterNot elimLits
      val newPredConj =
        predConj.updateLitsSubset(newPosLits, predConj.negativeLits, conj.order)

      conj.updatePredConj(newPredConj)(conj.order)
    }

    private def hasImpliedIneqConstraints(v : VariableTerm,
                                          lower : IdealInt,
                                          upper : IdealInt,
                                          ineqs : InEqConj) : Boolean =
      ineqs forall { lc =>
        !(lc.variables contains v) ||
        (lc.variables.size == 1 && lc.constants.isEmpty &&
         (lc.leadingCoeff match {
            case IdealInt.ONE       => -lc.constant <= lower
            case IdealInt.MINUS_ONE => lc.constant >= upper
            case _                  => false
          }))
      }
  }

  override val reducerPlugin : ReducerPluginFactory = ReducerFactory

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean = true
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}
