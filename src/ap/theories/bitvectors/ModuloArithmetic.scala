/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2022 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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
                               ReducerPluginFactory, NegatedConjunctions}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import LinearCombination.SingleTerm
import ap.basetypes.IdealInt
import ap.types.{Sort, ProxySort, SortedIFunction, SortedPredicate,
                 MonoSortedIFunction}
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
 */
object ModuloArithmetic extends Theory {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  protected[bitvectors] val debug = false
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  protected[bitvectors] val directlyEncodeExtract = false

  private val AC = Debug.AC_MODULO_ARITHMETIC

  override def toString = "ModuloArithmetic"

  // TODO: move the following methods to IdealInt class, optimise

  protected[bitvectors] def pow2(bits : Int) : IdealInt =
    IdealInt.pow2(bits)

  protected[bitvectors] def pow2(bits : IdealInt) : IdealInt =
    IdealInt.pow2(bits)

  protected[bitvectors] def pow2Mod(bits : IdealInt,
                                    modulus : IdealInt) : IdealInt =
    IdealInt.pow2Mod(bits, modulus)

  protected[bitvectors] def pow2MinusOne(bits : Int) : IdealInt =
    IdealInt.pow2MinusOne(bits)

  private def isPowerOf2(n : IdealInt) : Option[Int] =
    IdealInt.log2(n)

  //////////////////////////////////////////////////////////////////////////////
  // API methods that infer the right bit-width based on types
  // See http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
  // for an explanation of the operations
  
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
  def bvsge(t1 : ITerm, t2 : ITerm) : IFormula = bvsle(t2, t1)

  def zero_extend(addWidth : Int, t : ITerm) : ITerm =
    IFunApp(zero_extend, List(extractBitWidth(t), addWidth, t))
  def sign_extend(addWidth : Int, t : ITerm) : ITerm = {
    val w = extractBitWidth(t)
    cast2UnsignedBV(w + addWidth, cast2SignedBV(w, t))
  }

  //////////////////////////////////////////////////////////////////////////////

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

  /**
   * Cast a term to an integer term.
   */
  def cast2Int(t : ITerm) : ITerm = IFunApp(int_cast, List(t))

  //////////////////////////////////////////////////////////////////////////////

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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Modulo sorts, representing the interval
   * <code>[lower, upper]</code> with wrap-around arithmetic.
   */
  case class ModSort(lower : IdealInt, upper : IdealInt)
             extends ProxySort(Sort.Interval(Some(lower), Some(upper)))
             with    Theory.TheorySort {
    override val name : String = this match {
      case UnsignedBVSort(bits) =>
        "bv[" + bits + "]"
      case SignedBVSort(bits) =>
        "signed bv[" + bits + "]"
      case _ =>
        "mod[" + lower + ", " + upper + "]"
    }

    val theory = ModuloArithmetic.this
    
    val modulus = upper - lower + IdealInt.ONE

    import IExpression._

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(mod_cast(lower, upper, d))

    override val individuals : Stream[ITerm] =
      for (t <- super.individuals) yield mod_cast(lower, upper, t)
  }

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
   * Function to map the modulo-sorts back to integers. Semantically this
   * is just the identify function
   */
  val int_cast =
    new MonoSortedIFunction("int_cast",
                            List(Sort.AnySort), Sort.Integer, true, false)

  //////////////////////////////////////////////////////////////////////////////

  protected[bitvectors] def getLowerUpper(arguments : Seq[Term])
                                       : (IdealInt, IdealInt) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC,
      arguments(0).asInstanceOf[LinearCombination].isConstant &&
      arguments(1).asInstanceOf[LinearCombination].isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val lower = arguments(0).asInstanceOf[LinearCombination].constant
    val upper = arguments(1).asInstanceOf[LinearCombination].constant
    (lower, upper)
  }

  protected[bitvectors] def getModulus(a : Atom) : IdealInt = {
    val (lower, upper) = getLowerUpper(a)
    upper - lower + 1
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

    private def doIComputeSorts(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val indexes =
        for (IIntLit(IdealInt(n)) <- arguments take indexArity) yield n
      if (indexes.size < indexArity) {
        // this means that some of the indexes are symbolic, we just specify
        // argument sorts to be AnySort
        anySorts
      } else {
        computeSorts(indexes)
      }
    }

    private def doComputeSorts(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      val indexes =
        for (lc <- arguments take indexArity)
        yield lc.asInstanceOf[LinearCombination0].constant.intValueSafe
      computeSorts(indexes)
    }

    private lazy val anySorts =
      ((for (_ <- 0 until indexArity) yield Sort.Integer) ++
         (for (_ <- 0 until bvArity) yield Sort.AnySort),
       Sort.AnySort)

    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) =
      doIComputeSorts(arguments)
    
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) =
      doComputeSorts(arguments)
    
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
    
    def toPredicate : SortedPredicate =
      new SortedPredicate(_name, indexArity + bvArity + 1) {
        def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
          val (args, res) = doIComputeSorts(arguments)
          args ++ List(res)
        }
        
        def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
          val (args, res) = doComputeSorts(arguments)
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

  // Arguments: old_width, additional_bits, number
  // Result:    number mod 2^(old_width + additional_bits)

  object ZeroExtend
         extends IndexedBVOp("zero_extend", 2, 1) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      (List(Sort.Integer, Sort.Integer, UnsignedBVSort(indexes(0))),
       UnsignedBVSort(indexes(0) + indexes(1)))
    }
  }

  val zero_extend = ZeroExtend

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

  class BVOrder(_name : String) extends SortedPredicate(_name, 3) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] =
      arguments.head match {
        case IIntLit(IdealInt(n)) =>
          List(Sort.Integer, UnsignedBVSort(n), UnsignedBVSort(n))
        case _ =>
          // this means that some of the indexes are symbolic, we just specify
          // argument sorts to be AnySort
          List(Sort.Integer, Sort.AnySort, Sort.AnySort)
      }
        
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      val n = arguments.head.asInstanceOf[LinearCombination0]
                       .constant.intValueSafe
      List(Sort.Integer, UnsignedBVSort(n), UnsignedBVSort(n))
    }
        
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  val bv_ult           = new BVOrder("bv_ult")
  val bv_ule           = new BVOrder("bv_ule")
  val bv_slt           = new BVOrder("bv_slt")
  val bv_sle           = new BVOrder("bv_sle")

  //////////////////////////////////////////////////////////////////////////////

  val functions = List(
    mod_cast,
    int_cast,
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
    bv_comp,
    zero_extend
  )

  val otherPreds = List(bv_ult, bv_ule, bv_slt, bv_sle)

  val (predicates, preAxioms, order, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions, extraPredicates = otherPreds)

  val _bv_extract = functionTranslation(bv_extract)

  // We only keep the functionality axiom for the bv_extract function
  val axioms =
    (Conjunction.conj(preAxioms, order).iterator filter (
       _.predicates == Set(_bv_extract))).next

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    for (f <- functions) yield (f, functionTranslation(f))
  val functionalPredicates =
    (functionPredicateMapping map (_._2)).toSet

  val predicateMatchConfig: Signature.PredicateMatchConfig =
    (for (p <- predicates.toSet --
           List(_mod_cast, _l_shift_cast, _r_shift_cast, _bv_extract))
     yield (p -> Signature.PredicateMatchStatus.None)).toMap
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  override val singleInstantiationPredicates = predicates.toSet

  //////////////////////////////////////////////////////////////////////////////

  import ModPreprocessor.{Preproc, VisitorArg}

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) =
    (Preproc.visit(
        f, VisitorArg(None)).res.asInstanceOf[IFormula],
     signature)

  override def iPostprocess(f : IFormula, signature : Signature) : IFormula =
    ModPostprocessor(f)

  override def evalFun(f : IFunApp) : Option[ITerm] =
    if (f.args forall (isLit _)) {
      val sort = Sort sortOf f
      val res = Preproc.visit(f, VisitorArg(None))
      if (res.isConstant)
        Some(IIntLit(res.lowerBound))
      else
        None
    } else {
      None
    }

  override def evalPred(a : IAtom) : Option[Boolean] =
    if (a.args forall (isLit _)) {
      Preproc.visit(a, VisitorArg(None)).res match {
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

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction =
    ModPreprocessor.preprocess(f, order)

  //////////////////////////////////////////////////////////////////////////////

  val MultTheory = GroebnerMultiplication

  override val dependencies : Iterable[Theory] = List(MultTheory)

  val plugin = Some(ModPlugin)

  override val reducerPlugin : ReducerPluginFactory = ModReducer.ReducerFactory

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean = true
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}
