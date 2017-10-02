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
import ap.util.{Debug, IdealRange, LRUCache}

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

  class BVNAryOpPred(_name : String, _arity : Int)
        extends SortedPredicate(_name, _arity + 2) {
    def iArgumentSorts(arguments : Seq[ITerm]) : Seq[Sort] = {
      val IIntLit(bits) = arguments(0)
      val sort = UnsignedBVSort(bits.intValueSafe)
      Sort.Integer :: List.fill(_arity + 1)(sort)
    }
    def argumentSorts(arguments : Seq[Term]) : Seq[Sort] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val bits = arguments(0).asInstanceOf[LinearCombination].constant
      val sort = UnsignedBVSort(bits.intValueSafe)
      Sort.Integer :: List.fill(_arity + 1)(sort)
    }
    override def sortConstraints(arguments : Seq[Term])
                                (implicit order : TermOrder) : Formula =
      argumentSorts(arguments).last membershipConstraint arguments.last
  }

  class BVNAryOp(_name : String, _arity : Int)
        extends SortedIFunction(_name, _arity + 1, true, true) {
    def iFunctionType(arguments : Seq[ITerm]) : (Seq[Sort], Sort) = {
      val IIntLit(bits) = arguments(0)
      val sort = UnsignedBVSort(bits.intValueSafe)
      (Sort.Integer :: List.fill(_arity)(sort), sort)
    }
    def functionType(arguments : Seq[Term]) : (Seq[Sort], Sort) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
        arguments(0).asInstanceOf[LinearCombination].isConstant)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val bits = arguments(0).asInstanceOf[LinearCombination].constant
      val sort = UnsignedBVSort(bits.intValueSafe)
      (Sort.Integer :: List.fill(_arity)(sort), sort)
    }
    def iResultSort(arguments : Seq[ITerm]) : Sort = iFunctionType(arguments)._2
    def resultSort(arguments : Seq[Term]) : Sort = functionType(arguments)._2
    def toPredicate : SortedPredicate = new BVNAryOpPred(name, _arity)
  }

  //////////////////////////////////////////////////////////////////////////////

  // Arguments: N1, N2, number mod 2^N1, number mod 2^N2
  // Result:    number mod (N1 * N2)
  val bv_concat        = new IFunction("bv_concat",      4, true, true)
  
  // Arguments: N1, N2, N3, number mod 2^(N1 + N2 + N3)
  // Result:    number mod 2^N2
  val bv_extract       = new IFunction("bv_extract",     4, true, true)

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
  val bv_mul           = new BVNAryOp ("bv_mul", 2)
  val bv_udiv          = new BVNAryOp ("bv_udiv",2)
  val bv_sdiv          = new BVNAryOp ("bv_sdiv",2)
  val bv_urem          = new BVNAryOp ("bv_urem",2)
  val bv_srem          = new BVNAryOp ("bv_srem",2)
  val bv_smod          = new BVNAryOp ("bv_smod",2)
  val bv_shl           = new BVNAryOp ("bv_shl", 2)
  val bv_lshr          = new BVNAryOp ("bv_lshr",2)
  val bv_ashr          = new BVNAryOp ("bv_ashr",2)

  val bv_xor           = new BVNAryOp ("bv_xor", 2)
  val bv_xnor          = new BVNAryOp ("bv_xnor",2)

  // Arguments: N, number mod 2^N, number mod 2^N
  // Result:    number mod 2
  val bv_comp          = new IFunction("bv_comp",        3, true, true)

  // Arguments: N, number mod 2^N, number mod 2^N
  val bv_ult           = new Predicate("bv_ult",         3) // X
  val bv_ule           = new Predicate("bv_ule",         3) // X
  val bv_slt           = new Predicate("bv_slt",         3) // X
  val bv_sle           = new Predicate("bv_sle",         3) // X

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
        case BVPred(`bv_not`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), a(0) - a(1) - 1, a(2)))
        case BVPred(`bv_neg`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), -a(1), a(2)))
        case BVPred(`bv_add`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), a(1) + a(2), a(3)))
        case BVPred(`bv_sub`) =>
          _mod_cast(List(l(0), bits2Range(a(0)), a(1) - a(2), a(3)))

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

          val antecedent =
            modLit0 & modLit1 &
            lb <= v(0) & v(0) <= ub &
            lb <= v(1) & v(1) <= ub

          val predicate = a.pred match {
            case `bv_slt` => v(0) < v(1)
            case `bv_sle` => v(0) <= v(1)
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

  private val SPLIT_LIMIT = IdealInt(1000)

  /**
   * Splitter handles the splitting of modulo-operations, when no other
   * inference steps are possible anymore.
   */
  private object Splitter extends TheoryProcedure {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] =  {
//println("splitter " + goal.facts)
      val castPreds = goal.facts.predConj.positiveLitsWithPred(_mod_cast)
      val reducer = goal.reduceWithFacts
      implicit val order = goal.order
      import TerForConvenience._

      // find simple mod_cast predicates that can be replaced by equations
      var simpleElims : List[Plugin.Action] = List()

      // find a mod_cast predicate that can be split into a small number of
      // cases
      var bestSplitNum = SPLIT_LIMIT
      var bestSplitPred : Option[(Atom, IdealInt, IdealInt,
                                  List[Formula], ModSort)] = None

      // find a predicate that has to be eliminated through a quantifier
      var someQuantPred : Option[Atom] = None

      val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

      for (a <- castPreds) {
        var assumptions : List[Formula] = List(a)

        val lBound =
          if (proofs)
            for ((b, assum) <- reducer lowerBoundWithAssumptions a(2)) yield {
              assumptions = InEqConj(assum, order) :: assumptions
              b
            }
          else
            reducer lowerBound a(2)

        val uBound =
          if (lBound.isDefined) {
            if (proofs)
              for ((b, assum) <- reducer upperBoundWithAssumptions a(2)) yield {
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
                bestSplitPred =
                  Some((a, lowerFactor, upperFactor, assumptions, sort))
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

        val Some((a, lowerFactor, upperFactor, assumptions, sort)) =
          bestSplitPred
        val cases =
          (for (n <- IdealRange(lowerFactor, upperFactor + 1).iterator;
                f = conj(a(2) === a(3) + (n * sort.modulus));
                if !f.isFalse)
           yield (f, List())).toList

        List(Plugin.RemoveFacts(a),
             Plugin.AxiomSplit(assumptions,
                               cases,
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

    def finalReduce(conj : Conjunction) = conj
  }

  override val reducerPlugin : ReducerPluginFactory = ReducerFactory

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean = true
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}