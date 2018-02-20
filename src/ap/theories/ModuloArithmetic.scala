/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.Signature
import ap.parser._
import ap.parameters.{Param, ReducerSettings, GoalSettings}
import ap.terfor.{Term, VariableTerm, TermOrder, Formula, ComputationLogger,
                  TerForConvenience}
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               ReducerPluginFactory, IdentityReducerPlugin,
                               ReducerPlugin, NegatedConjunctions}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import ap.terfor.substitutions.VariableShiftSubst
import ap.basetypes.IdealInt
import ap.types.{Sort, ProxySort, SortedIFunction, SortedPredicate}
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.theories.nia.GroebnerMultiplication
import ap.util.{Debug, IdealRange, LRUCache, Seqs}

import scala.collection.mutable.{ArrayBuffer, Map => MMap, HashSet => MHashSet}

/**
 * Theory for performing bounded modulo-arithmetic (arithmetic modulo some
 * number N). This in particular includes bit-vector/machine arithmetic.
 *
 * Class under construction ...
 */
object ModuloArithmetic extends Theory {

  private val AC = Debug.AC_MODULO_ARITHMETIC

  override def toString = "ModuloArithmetic"

  val MultTheory = GroebnerMultiplication

  // TODO: move the following methods to IdealInt class, optimise

  private def pow2(bits : Int) : IdealInt =
    IdealInt(2) pow bits

  private def pow2(bits : IdealInt) : IdealInt =
    IdealInt(2) pow bits.intValueSafe

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
  def extract(begin : Int, end : Int, t : ITerm) : ITerm = {
    val width = extractBitWidth(t)
    IFunApp(bv_extract,
            List(width - begin - 1, begin - end + 1, end, t))
  }

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

    override def augmentModelTermSet(model : Conjunction,
                                     terms : MMap[(IdealInt, Sort), ITerm])
                                    : Unit = {
      // at the moment, just a naive traversal that introduces mod_cast terms
      // for every integer literal in the model

      import IExpression._

      for (lc <- model.arithConj.positiveEqs)
        terms.put((-lc.constant, this), mod_cast(lower, upper, -lc.constant))

      for (a <- model.groundAtoms.iterator; lc <- a.iterator)
        terms.put((lc.constant, this), mod_cast(lower, upper, lc.constant))
    }
  }

  /**
   * Object to create and recognise modulo sorts representing
   * unsigned bit-vectors.
   */
  object UnsignedBVSort {
    def apply(bits : Int) : ModSort =
      ModSort(IdealInt.ZERO, pow2MinusOne(bits))
    def unapply(s : Sort) : Option[Int] = s match {
      case ModSort(IdealInt.ZERO, upper)
        if (upper.signum > 0 && (upper & (upper + 1)).isZero) =>
          Some(upper.getHighestSetBit + 1)
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
   * The function is applied as <code>shift_cast(lower, upper, t, n)</code>.
   * <code>n</code> can be negative, in which case rounding towards zero is
   * performed.
   */
  val l_shift_cast = new ShiftFunction("l_shift_cast", _l_shift_cast)

  /**
   * Shift the term <code>shifted</code> a number of bits to the left,
   * staying within the given sort.
   */
  def shiftLeft(sort : ModSort, shifted : ITerm, bits : ITerm) : ITerm =
    IFunApp(l_shift_cast, List(sort.lower, sort.upper, shifted, bits))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generic class to represent families of functions, indexed by a vector of
   * bit-widths.
   */
  abstract class IndexedBVOp(_name : String, indexArity : Int, bvArity : Int)
           extends SortedIFunction(_name, indexArity + bvArity, true, true) {

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

  // Arguments: N1, N2, N3, number mod 2^(N1 + N2 + N3)
  // Result:    number mod 2^N2

  object BVExtract extends IndexedBVOp("bv_extract", 3, 1) {
    def computeSorts(indexes : Seq[Int]) : (Seq[Sort], Sort) = {
      (List(Sort.Integer, Sort.Integer, Sort.Integer,
            UnsignedBVSort(indexes(0) + indexes(1) + indexes(2))),
       UnsignedBVSort(indexes(1)))
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

  // Arguments: N, number mod 2^N, number mod 2^N
  // Result:    number mod 2
  val bv_comp          = new IFunction("bv_comp",        3, true, true)

  // Arguments: N, number mod 2^N, number mod 2^N
  val bv_ult           = new Predicate("bv_ult", 3) // X
  val bv_ule           = new Predicate("bv_ule", 3) // X
  val bv_slt           = new Predicate("bv_slt", 3) // X
  val bv_sle           = new Predicate("bv_sle", 3) // X

  //////////////////////////////////////////////////////////////////////////////

  val functions = List(
    mod_cast,
    l_shift_cast,
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

  val (functionalPredSeq, _, preOrder, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)
  val axioms = Conjunction.TRUE

  val functionPredicateMapping = functions zip functionalPredSeq
  val functionalPredicates = functionalPredSeq.toSet

  val order = preOrder extendPred otherPreds

  val predicates = otherPreds ++ functionalPredSeq
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  override val singleInstantiationPredicates = predicates.toSet

  //////////////////////////////////////////////////////////////////////////////

  private case class VisitorArg(modN : Option[IdealInt],
                                boundVarRanges : List[(Option[IdealInt],
                                                       Option[IdealInt])],
                                underQuantifier : Boolean) {
    import IExpression._

    def addMod(n : IdealInt) = modN match {
      case Some(oldN) if (oldN divides n) =>
        this.notUnderQuantifier
      case _ =>
        copy(modN = Some(n), underQuantifier = false)
    }

    def divideMod(divisor : IdealInt) = modN match {
      case Some(oldN) => {
        val g = oldN gcd divisor
        if (g > IdealInt.ONE)
          copy(modN = Some(oldN / g), underQuantifier = false)
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
                 if (lowerBound == null) null else (lowerBound / divisor),
                 if (upperBound == null) null else (upperBound / divisor))
    }
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

      case IFunApp(`bv_concat`, Seq(_, IIntLit(IdealInt(n)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt divideMod pow2(n), ctxt.noMod))
      case IFunApp(`bv_extract`,
                   Seq(_, IIntLit(IdealInt(n1)), IIntLit(IdealInt(n2)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod, ctxt.noMod,
                     ctxt addMod pow2(n1 + n2)))

      case IFunApp(`bv_not` | `bv_neg` |
                   `bv_add` | `bv_sub` | `bv_mul` | `bv_srem`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        // TODO: handle bit-width argument correctly
        UniSubArgs(ctxt addMod pow2(n))

      case IFunApp(`bv_shl`,
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

    def postVisit(t : IExpression,
                  ctxt : VisitorArg, subres : Seq[VisitorRes]) : VisitorRes = {
//      println("" + t + ", " + ctxt)
      val res = t match {
        case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _)) =>
          subres.last.modCastHelp(lower, upper, ctxt) match {
            case null => VisitorRes.update(t, subres)
            case res  => res
          }

        case IFunApp(`bv_concat`, Seq(_, IIntLit(IdealInt(bits)), _*)) =>
          (subres(2) * pow2(bits)) + subres(3)
/*
   This is currently handled in the Theory.preprocess method
   (but has to be further optimised)

        case IFunApp(`bv_extract`, Seq(_, IIntLit(IdealInt(n1)),
                                          IIntLit(IdealInt(n2)), _*)) =>
          (subres.last eDiv pow2(n2)).modCastPow2(n1, ctxt)
*/

        case IFunApp(`bv_not`, Seq(IIntLit(IdealInt(bits)), _)) =>
          (subres.last * IdealInt.MINUS_ONE +
             IdealInt.MINUS_ONE).modCastPow2(bits, ctxt)
        case IFunApp(`bv_neg`, Seq(IIntLit(IdealInt(bits)), _)) =>
          (subres.last * IdealInt.MINUS_ONE).modCastPow2(bits, ctxt)

        case IFunApp(`bv_add`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + subres(2)).modCastPow2(bits, ctxt)
        case IFunApp(`bv_sub`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + (subres(2) * IdealInt.MINUS_ONE)).modCastPow2(bits, ctxt)

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_mul`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(1).isConstant)
            (subres(2) * subres(1).lowerBound).modCastPow2(bits, ctxt)
          else if (subres(2).isConstant)
            (subres(1) * subres(2).lowerBound).modCastPow2(bits, ctxt)
          else
            (subres(1) * subres(2)).modCastPow2(bits, ctxt)

        // TODO: move this clause to the multiplication theory?
        case IFunApp(MulTheory.Mul(), Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(1).isConstant)
            subres(2) * subres(1).lowerBound
          else if (subres(2).isConstant)
            subres(1) * subres(2).lowerBound
          else
            VisitorRes.update(t, subres)

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`l_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
          if (subres(3).isConstant)
            (subres(2) * pow2(subres(3).lowerBound max IdealInt.ZERO))
                .modCast(lower, upper, ctxt)
          else
            VisitorRes.update(t, subres)

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

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_and`, Seq(IIntLit(IdealInt(bits)), _*)) => {
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
                  bv_extract(bits - length, length, 0, arg.resTerm),
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
                          bv_extract(bits - offset, len, offset - len, v(1)) ===
                          (if (bit)
                             bv_extract(bits - offset, len, offset - len, v(0))
                           else
                             i(0))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  UnsignedBVSort(bits).eps(
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
            case (false, false) =>
              VisitorRes.update(t, subres)
          }
        }

        case IFunApp(`bv_or`, Seq(IIntLit(IdealInt(bits)), _*)) => {
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
                  bv_extract(length, offset, 0, arg.resTerm) + pattern,
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
                          bv_extract(bits - offset, len, offset - len, v(1)) ===
                          (if (bit)
                             i(pow2MinusOne(len))
                           else
                             bv_extract(bits - offset, len, offset - len, v(0)))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  UnsignedBVSort(bits).eps(
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
            case (false, false) =>
              VisitorRes.update(t, subres)
          }
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
          VisitorRes(subres(1).resTerm < subres(2).resTerm)
        case IAtom(`bv_ule`, _) =>
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
//      println(res)
      res
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) = {
    (Preproc.visit(f,
        VisitorArg(None, List(), false)).res.asInstanceOf[IFormula],
     signature)
  }

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

        case BVPred(`bv_extract`) => { // to be improved!
          val bits1 =
            a(1).asInstanceOf[LinearCombination0].constant.intValueSafe
          val bits2 =
            a(2).asInstanceOf[LinearCombination0].constant.intValueSafe

          val castSort = UnsignedBVSort(bits1 + bits2)
          val remSort =  UnsignedBVSort(bits2)

          val subst = VariableShiftSubst(0, 1, order)
          val pred = _mod_cast(List(l(0), l(castSort.upper),
                                    subst(a(3)),
                                    subst(a(4))*remSort.modulus + v(0)))

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

        case `_mod_cast` | `_l_shift_cast` =>
          a

        case BVPred(_) => {
          Console.err.println("Warning: don't know how to handle " + a)
          (incompletenessFlag.value)(0) = true
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

  // a simple flag to detect problems with operators that are not yet
  // supported
  // TODO: add support for all operators

  val incompletenessFlag =
    new scala.util.DynamicVariable[Array[Boolean]] (Array(false))

  //////////////////////////////////////////////////////////////////////////////

  override val dependencies : Iterable[Theory] = List(MultTheory)

  def plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      
        val actions1 = modCastActions(goal)
        val actions2 = shiftCastActions(goal)

        val resActions1 =
          if (actions1 exists (_.isInstanceOf[Plugin.AxiomSplit]))
            // delayed splitting through a separate task
            List(Plugin.ScheduleTask(ModCastSplitter, 0))
          else
            actions1

        val resActions2 =
          if (actions2 exists (_.isInstanceOf[Plugin.AxiomSplit]))
            // delayed splitting through a separate task
            List(Plugin.ScheduleTask(ShiftCastSplitter, 0))
          else
            actions2

        resActions1 ++ resActions2
    }
  })

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
              if (!assum.isEmpty)
                assumptions = InEqConj(assum, order) :: assumptions
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
                  if (!assum.isEmpty)
                    assumptions = InEqConj(assum, order) :: assumptions
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
          case (_, Some(upper)) if upper.signum < 0 => {
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
          case (Some(lower), Some(upper)) if simpleElims.isEmpty => {
            // need to do some splitting        
            val cases = (upper - lower + 1).intValueSafe
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

        val lBound =
          if (proofs)
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(2)) yield {
              if (!assum.isEmpty)
                assumptions = InEqConj(assum, order) :: assumptions
              b
            }
          else
            reducer lowerBound a(2)

        val uBound =
          if (lBound.isDefined) {
            if (proofs)
              for ((b, assum) <- reducer upperBoundWithAssumptions a(2)) yield {
                if (!assum.isEmpty)
                  assumptions = InEqConj(assum, order) :: assumptions
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
    Debug.assertPre(AC, a.pred == _mod_cast)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val lt1 = a(2).leadingTerm
    val lt2 = a(3).leadingTerm
    if (order.compare(lt1, lt2) > 0)
      lt1
    else
      lt2
  }

  /**
   * Compute the effective leading coefficient of the modulo atom <code>a</code>
   * for simplifying modulo the given <code>modulus</code>.
   */
  private def effectiveLeadingCoeff(a : Atom,
                                    modulus : IdealInt,
                                    order : TermOrder) : IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, a.pred == _mod_cast)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val aModulus = getModulus(a)
    val modulusLCM = aModulus lcm modulus

    val leadingCoeff =
      if (a(3).isEmpty || order.compare(a(2).leadingTerm, a(3).leadingTerm) > 0)
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

  private def extractModulos(atoms : Seq[Atom], order : TermOrder)
                            (t : Term) : Iterator[Atom] =
    for (a <- atoms.iterator;
         if a.pred == _mod_cast;
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
      if (logger.isLogging) {
        // TODO
        ReducerPlugin.UnchangedResult
      } else {
        implicit val order = predConj.order
        import TerForConvenience._

        // TODO: eliminate mod_cast arguments with large coefficients

        {
          // First try to eliminate some modulo atoms
          ReducerPlugin.rewritePreds(predConj,
                                     List(_mod_cast, _l_shift_cast),
                                     order) { a =>
              a.pred match {
                case `_mod_cast` =>
                  (reducer lowerBound a(2), reducer upperBound a(2)) match {
          
                    case (Some(lb), Some(ub)) => {
                      val sort@ModSort(sortLB, sortUB) =
                        (SortedPredicate argumentSorts a).last
                
                      val lowerFactor = (lb - sortLB) / sort.modulus
                      val upperFactor = -((sortUB - ub) / sort.modulus)

                      if (lowerFactor == upperFactor)
                        a(2) === a(3) + (lowerFactor * sort.modulus)
                      else
                        a
                    }
            
                    case _ =>
                      a
                  }

                case `_l_shift_cast` =>
                  if (a(2).isZero) {
                    Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order)
                  } else if (a(3).isConstant) {
                    Atom(_mod_cast,
                         Array(a(0), a(1),
                               a(2) * pow2(a(3).constant max IdealInt.ZERO),
                               a(4)),
                         order)
                  } else {
                    (reducer lowerBound a(3)) match {
                      case Some(lb) if lb.signum > 0 =>
                        Atom(_l_shift_cast,
                             Array(a(0), a(1),
                                   a(2) * pow2(lb), a(3) - lb, a(4)),
                             order)
                      case _ =>
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
                                     order) {
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
                        LinearCombination.SingleTerm(resVar : VariableTerm)),
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
                     Seq(_, _, _,
                         LinearCombination.SingleTerm(resVar : VariableTerm)),
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
