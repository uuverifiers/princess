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

import ap.parser._
import ap.parameters.{Param, ReducerSettings}
import ap.terfor.{Term, TermOrder, Formula, ComputationLogger,
                  TerForConvenience}
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPluginFactory, IdentityReducerPlugin,
                               ReducerPlugin}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import ap.terfor.substitutions.VariableShiftSubst
import ap.basetypes.IdealInt
import ap.types.{Sort, ProxySort, SortedIFunction, SortedPredicate}
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.util.{Debug, IdealRange}

import scala.collection.mutable.{ArrayBuffer, Map => MMap}

/**
 * Theory for performing bounded modulo-arithmetic (arithmetic modulo some
 * number N). This in particular includes bit-vector/machine arithmetic.
 *
 * Class under construction ...
 */
object ModuloArithmetic extends Theory {

  private val AC = Debug.AC_MODULO_ARITHMETIC

  override def toString = "ModuloArithmetic"

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

  // Function for mapping any number to an interval [lower, upper].
  // The function is applied as mod_cast(lower, upper, number)

  val _mod_cast = new SortedPredicate("mod_cast", 4) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      List(Sort.Integer, Sort.Integer, Sort.Integer, ModSort(lower, upper))
    }
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant &&
        arguments(1).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val lower = arguments(0).asInstanceOf[LinearCombination].constant
      val upper = arguments(1).asInstanceOf[LinearCombination].constant
      List(Sort.Integer, Sort.Integer, Sort.Integer, ModSort(lower, upper))
    }
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  val mod_cast = new SortedIFunction("mod_cast", 3, true, true) {
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(lower) = arguments(0)
      val IIntLit(upper) = arguments(1)
      (List(Sort.Integer, Sort.Integer, Sort.Integer), ModSort(lower, upper))
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant &&
        arguments(1).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val lower = arguments(0).asInstanceOf[LinearCombination].constant
      val upper = arguments(1).asInstanceOf[LinearCombination].constant
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

  class BVNAryOpPred(_name : String, _arity : Int)
        extends SortedPredicate(_name, _arity + 2) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
      val IIntLit(modulus) = arguments(0)
      Sort.Integer :: List.fill(_arity + 1)(ModSort(0, modulus - 1))
    }
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val modulus = arguments(0).asInstanceOf[LinearCombination].constant
      Sort.Integer :: List.fill(_arity + 1)(ModSort(0, modulus - 1))
    }
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  class BVNAryOp(_name : String, _arity : Int)
        extends SortedIFunction(_name, _arity + 1, true, true) {
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(modulus) = arguments(0)
      val sort = ModSort(0, modulus - 1)
      (Sort.Integer :: List.fill(_arity)(sort), sort)
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val modulus = arguments(0).asInstanceOf[LinearCombination].constant
      val sort = ModSort(0, modulus - 1)
      (Sort.Integer :: List.fill(_arity)(sort), sort)
    }
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
    def toPredicate : SortedPredicate = new BVNAryOpPred(name, _arity)
  }

  //////////////////////////////////////////////////////////////////////////////

  // Arguments: N1, N2, number mod N1, number mod N2
  // Result:    number mod (N1 * N2)
  val mod_concat        = new IFunction("mod_concat",      4, true, true)
  
  // Arguments: N1, N2, N3, number mod (N1 * N2 * N3)
  // Result:    number mod N2
  val mod_extract       = new IFunction("mod_extract",     4, true, true)

  // Arguments: N, number mod N
  // Result:    number mod N
  val mod_not           = new BVNAryOp ("mod_not", 1) // X
  val mod_neg           = new BVNAryOp ("mod_neg", 1) // X

  // Arguments: N, number mod N, number mod N
  // Result:    number mod N
  val mod_and           = new BVNAryOp ("mod_and", 2)
  val mod_or            = new BVNAryOp ("mod_or",  2)
  val mod_add           = new BVNAryOp ("mod_add", 2) // X
  val mod_sub           = new BVNAryOp ("mod_sub", 2) // X
  val mod_mul           = new BVNAryOp ("mod_mul", 2)
  val mod_udiv          = new BVNAryOp ("mod_udiv",2)
  val mod_sdiv          = new BVNAryOp ("mod_sdiv",2)
  val mod_urem          = new BVNAryOp ("mod_urem",2)
  val mod_srem          = new BVNAryOp ("mod_srem",2)
  val mod_smod          = new BVNAryOp ("mod_smod",2)
  val mod_shl           = new BVNAryOp ("mod_shl", 2)
  val mod_lshr          = new BVNAryOp ("mod_lshr",2)
  val mod_ashr          = new BVNAryOp ("mod_ashr",2)

  val mod_xor           = new BVNAryOp ("mod_xor", 2)
  val mod_xnor          = new BVNAryOp ("mod_xnor",2)

  // Arguments: N, number mod N, number mod N
  // Result:    number mod 2
  val mod_comp          = new IFunction("mod_comp",        3, true, true)

  // Arguments: N, number mod N, number mod N
  val mod_ult           = new Predicate("mod_ult",         3) // X
  val mod_ule           = new Predicate("mod_ule",         3) // X
  val mod_slt           = new Predicate("mod_slt",         3) // X
  val mod_sle           = new Predicate("mod_sle",         3) // X

  //////////////////////////////////////////////////////////////////////////////

  val functions = List(
    mod_cast,
    mod_concat,
    mod_extract,
    mod_not,
    mod_neg,
    mod_and,
    mod_or,
    mod_add,
    mod_sub,
    mod_mul,
    mod_udiv,
    mod_sdiv,
    mod_urem,
    mod_srem,
    mod_smod,
    mod_shl,
    mod_lshr,
    mod_ashr,
    mod_xor,
    mod_xnor,
    mod_comp
  )

  val otherPreds = List(mod_ult, mod_ule, mod_slt, mod_sle)

  val (functionalPredSeq, axioms, preOrder, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  val functionPredicateMapping = functions zip functionalPredSeq
  val functionalPredicates = functionalPredSeq.toSet

  val order = preOrder extendPred otherPreds

  val predicates = otherPreds ++ functionalPredSeq
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  override val singleInstantiationPredicates = predicates.toSet

  //////////////////////////////////////////////////////////////////////////////

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    import TerForConvenience._
    
    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case BVPred(`mod_not`) =>
          _mod_cast(List(l(0), a(0) - 1, a(0) - a(1) - 1, a(2)))
        case BVPred(`mod_neg`) =>
          _mod_cast(List(l(0), a(0) - 1, -a(1), a(2)))
        case BVPred(`mod_add`) =>
          _mod_cast(List(l(0), a(0) - 1, a(1) + a(2), a(3)))
        case BVPred(`mod_sub`) =>
          _mod_cast(List(l(0), a(0) - 1, a(1) - a(2), a(3)))

        case `mod_ult` =>
          a(1) < a(2)
        case `mod_ule` =>
          a(1) <= a(2)

        case `mod_slt` | `mod_sle` => { // TODO: optimise
          val modulus = a(0).asInstanceOf[LinearCombination0].constant
          val lb = l(-(modulus / 2))
          val ub = l(modulus / 2 - 1)
          val subst = VariableShiftSubst(0, 2, order)
          val modLit0 = _mod_cast(List(lb, ub, subst(a(1)), l(v(0))))
          val modLit1 = _mod_cast(List(lb, ub, subst(a(2)), l(v(1))))

          val antecedent =
            modLit0 & modLit1 &
            lb <= v(0) & v(0) <= ub &
            lb <= v(1) & v(1) <= ub

          val predicate = a.pred match {
            case `mod_slt` => v(0) < v(1)
            case `mod_sle` => v(0) <= v(1)
          }

          if (negated)
            exists(2, antecedent & predicate)
          else
            forall(2, antecedent ==> predicate)
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

    val after2 = ReduceWithConjunction(Conjunction.TRUE,
                                       order,
                                       reducerSettings)(after1)

/*    println(f)
    println(after1)
    println(after2) */

    after2
  }  

  private object BVPred {
    val reverseMapping =
      (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap
    def unapply(p : Predicate) : Option[IFunction] = reverseMapping get p
  }

  //////////////////////////////////////////////////////////////////////////////

  def plugin = Some(new Plugin {
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val castPreds = goal.facts.predConj.positiveLitsWithPred(_mod_cast)
      if (castPreds.isEmpty)
        List()
      else
        List(Plugin.ScheduleTask(Splitter, 0))
    }
  })

  /**
   * Splitter handles the splitting of modulo-operations, when no other
   * inference steps are possible anymore.
   */
  private object Splitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
      val castPreds = goal.facts.predConj.positiveLitsWithPred(_mod_cast)
      val reducer = goal.reduceWithFacts
      implicit val order = goal.order
      import TerForConvenience._

      // find the best modulo operation to split
      var bestSplitNum = 1000000
      var bestSplitAction : Seq[Plugin.Action] = null

      var simpleElims : List[Plugin.Action] = List()
      var assumptions : List[Formula] = List()

      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      for (a <- castPreds) {
        assumptions = List(a)

        val lBound =
          if (proofs)
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(2)) yield {
              assumptions = InEqConj(assum, order) :: assumptions
              b
            }
          else
            reducer lowerBound a(2)

        val uBound =
          if (proofs)
            for ((b, assum) <- reducer upperBoundWithAssumptions a(2)) yield {
              assumptions = InEqConj(assum, order) :: assumptions
              b
            }
          else
            reducer upperBound a(2)

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

              if (caseNum < IdealInt(bestSplitNum)) {
                val cases =
                  (for (n <- IdealRange(lowerFactor, upperFactor + 1).iterator;
                        f = conj(a(2) === a(3) + (n * sort.modulus));
                        if !f.isFalse)
                   yield (f, List())).toList

                bestSplitNum = cases.size
                bestSplitAction = List(
                  Plugin.RemoveFacts(a),
                  Plugin.AxiomSplit(assumptions,
                                    cases,
                                    ModuloArithmetic.this))
              }
            }
          }
          case _ =>
            // nothing
        }
      }

      if (!simpleElims.isEmpty) {
        simpleElims
      } else if (bestSplitAction != null) {
        bestSplitAction
      } else {
        List()
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Reducer extends ReducerPlugin {
    object factory extends ReducerPluginFactory {
      def apply(conj : Conjunction, order : TermOrder) = Reducer
    }
    
    def passQuantifiers(num : Int) = this

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

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
        }
      }

    def finalReduce(conj : Conjunction) = conj
  }

  override val reducerPlugin : ReducerPluginFactory = Reducer.factory

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean = true
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}