/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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
      ModSort(IdealInt.ZERO, (IdealInt(2) pow bits) - IdealInt.ONE)
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
      val upper = IdealInt(2) pow (bits - 1)
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

  // function for mapping any number to an interval [lower, upper].
  // The function is applied as mod_cast(lower, upper, number)

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

  val mod_cast = new SortedIFunction("mod_cast", 3, true, false) {
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      (List(Sort.Integer, Sort.Integer, Sort.Integer), ModSort(lower, upper))
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      val (lower, upper) = getLowerUpper(arguments)
      (List(Sort.Integer, Sort.Integer, Sort.Integer), ModSort(lower, upper))
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

    def noMod =
      copy(modN = None, underQuantifier = false)

    def pushVar =
      copy(boundVarRanges = (None, None) :: boundVarRanges,
           underQuantifier = true)

    def notUnderQuantifier =
      copy(underQuantifier = false)

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

    def noModCastNeeded(lower : IdealInt, upper : IdealInt,
                        ctxt : VisitorArg) = {
      val modulus = upper - lower + IdealInt.ONE
      ctxt.modN match {
        case Some(n) if (n divides modulus) =>
          true
        case _ =>
          lowerBound != null && upperBound != null &&
          (lowerBound - lower) / modulus == -((upper - upperBound) / modulus)
      }
    }

    def modCast(lower : IdealInt, upper : IdealInt,
                ctxt : VisitorArg) : VisitorRes =
      if (noModCastNeeded(lower, upper, ctxt))
        this
      else
        VisitorRes(mod_cast(lower, upper, res.asInstanceOf[ITerm]),
                   lower, upper)
  }

  //////////////////////////////////////////////////////////////////////////////

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
      // Concat
      // Extract
      case IFunApp(`bv_not` | `bv_neg` | `bv_and` | `bv_or` |
                   `bv_add` | `bv_sub` | `bv_mul`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        UniSubArgs(ctxt addMod (IdealInt(2) pow n))
      case _ : IPlus | _ : ITimes | IFunApp(MulTheory.Mul(), _) => // IMPROVE
        UniSubArgs(ctxt.notUnderQuantifier)
      case _ =>
        UniSubArgs(ctxt.noMod)
    }

    def postVisit(t : IExpression,
                  ctxt : VisitorArg, subres : Seq[VisitorRes]) : VisitorRes = {
      println("" + t + ", " + ctxt)
      val res = t match {
        case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _))
          if subres.last.noModCastNeeded(lower, upper, ctxt) =>
            subres.last
        case t => 
          VisitorRes.update(t, subres)
      }
      println(res)
      res
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) = {
/*    (Preproc.visit(f,
        VisitorArg(None, List(), false)).res.asInstanceOf[IFormula],
     signature) */
    (f, signature)
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
      LinearCombination((IdealInt(2) pow bits) - IdealInt.ONE)
    }

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    import TerForConvenience._

//    println("init: " + f)

    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case BVPred(`bv_concat`) => {
          val shift = IdealInt(2) pow a(1).asInstanceOf[LinearCombination0]
                                          .constant.intValueSafe
          a(2) * shift + a(3) === a(4)
        }

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

        case BVPred(`bv_not`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), -a(1) - 1, a(2)))
        case BVPred(`bv_neg`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), -a(1), a(2)))
        case BVPred(`bv_add`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), a(1) + a(2), a(3)))
        case BVPred(`bv_sub`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), a(1) - a(2), a(3)))

        case BVPred(`bv_mul`) =>
          if (a(1).isConstant) {
            _mod_cast(List(l(0), bits2Range(a(0)), a(2) * a(1).constant, a(3)))
          } else if (a(2).isConstant) {
            _mod_cast(List(l(0), bits2Range(a(0)), a(1) * a(2).constant, a(3)))
          } else {
            val subst = VariableShiftSubst(0, 1, order)
            val mulPred = GroebnerMultiplication._mul(
                            List(subst(a(1)), subst(a(2)), l(v(0))))
            val castPred = 
              _mod_cast(List(l(0), bits2Range(a(0)), l(v(0)), subst(a(3))))
            if (negated)
              exists(mulPred & castPred)
            else
              forall(mulPred ==> castPred)
          }

        case BVPred(`bv_udiv`) => {
          val num   = a(1)
          val denom = a(2)
          val res   = a(3)

          if (denom.isConstant) {

            if (denom.constant.isZero) {
              res === bits2Range(a(0))
            } else {
              (res * denom <= num) & (res * denom > num - denom)
            }

          } else {

            val subst   = VariableShiftSubst(0, 1, order)
            val shNum   = subst(num)
            val shDenom = subst(denom)
            val shRes   = subst(res)

            val mulPred = GroebnerMultiplication._mul(
                            List(shRes, shDenom, l(v(0))))

            val ineqs   = (v(0) <= num) & (v(0) > num - denom)

            if (negated)
              exists(mulPred &
                     (((shDenom === 0) & (shRes === bits2Range(a(0)))) |
                      ((shDenom > 0) & ineqs)))
            else
              forall(mulPred ==>
                     (((shDenom === 0) ==> (shRes === bits2Range(a(0)))) &
                      ((shDenom > 0) ==> ineqs)))
          }
        }

        case BVPred(`bv_urem`) if a(2).isConstant => {
          val num   = a(1)
          val denom = a(2)
          val res   = a(3)

//          if (denom.isConstant) {

            if (denom.constant.isZero)
              res === num
            else
              _mod_cast(List(l(0), denom - 1, a(1), a(3)))

//          } else {
//            ... TODO
//          }
        }

        case BVPred(`bv_shl`) if a(2).isConstant =>
          _mod_cast(List(l(0), bits2Range(a(0)),
                         a(1) * (IdealInt(2) pow a(2).constant.intValueSafe),
                         a(3)))

        case `bv_ult` =>
          a(1) < a(2)
        case `bv_ule` =>
          a(1) <= a(2)

        case `bv_slt` | `bv_sle` => { // TODO: optimise
          val bits = a(0).asInstanceOf[LinearCombination0].constant.intValueSafe
          val modulus = IdealInt(2) pow bits
          val lb = l(-(modulus / 2))
          val ub = l(modulus / 2 - 1)
          val subst = VariableShiftSubst(0, 2, order)
          val modLit0 = _mod_cast(List(lb, ub, subst(a(1)), l(v(0))))
          val modLit1 = _mod_cast(List(lb, ub, subst(a(2)), l(v(1))))

          val antecedent = modLit0 & modLit1

          val predicate = a.pred match {
            case `bv_slt` => v(0) < v(1)
            case `bv_sle` => v(0) <= v(1)
          }

          val sort = SignedBVSort(bits)

          if (negated)
            existsSorted(List(sort, sort), antecedent & predicate)
          else
            forallSorted(List(sort, sort), antecedent ==> predicate)
        }

        case `_mod_cast` =>
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

  override val dependencies : Iterable[Theory] = List(GroebnerMultiplication)

  def plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val castPreds = goal.facts.predConj.positiveLitsWithPred(_mod_cast)
      if (castPreds.isEmpty) {
        List()
      } else {
        val actions = actionsForGoal(goal)
        if (actions exists (_.isInstanceOf[Plugin.AxiomSplit]))
          // delayed splitting through a separate task
          List(Plugin.ScheduleTask(Splitter, 0))
        else
          actions
      }
    }
  })

  private val SPLIT_LIMIT = IdealInt(20)

  /**
   * Splitter handles the splitting of modulo-operations, when no other
   * inference steps are possible anymore.
   */
  private object Splitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
//println("splitter " + goal.facts)
      actionsForGoal(goal)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

    private def actionsForGoal(goal : Goal) : Seq[Plugin.Action] =  {
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
        ReducerPlugin.UnchangedResult
      } else {
        implicit val order = predConj.order
        import TerForConvenience._

        {
          // First try to eliminate some modulo atoms
          ReducerPlugin.rewritePreds(predConj, List(_mod_cast), order) {
            a => (reducer lowerBound a(2), reducer upperBound a(2)) match {
          
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

          ReducerPlugin.rewritePreds(predConj, List(_mod_cast), order) {
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
                val newA = Atom(_mod_cast, Array(a(0), a(1), newA2, a(3)),
                                order)
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