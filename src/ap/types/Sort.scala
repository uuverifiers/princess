/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.types

import ap.basetypes.IdealInt
import ap.parser._
import ap.terfor.{Term, Formula, TermOrder, OneTerm, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.theories.Theory
import ap.util.Debug

import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

object Sort {

  private val AC = Debug.AC_TYPES

  /**
   * The sort of integers, which is also the default sort whenever
   * no sort is specified.
   */
  object Integer extends Sort {
    val name : String = "int"

    def membershipConstraint(t : ITerm) : IFormula =
      IExpression.i(true)

    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
      Conjunction.TRUE

    val cardinality : Option[IdealInt] = None

    val individuals : Stream[ITerm] =
      for (n <- Stream.iterate(IdealInt.ZERO){
                  n => if (n.signum <= 0) (-n+1) else -n
                })
      yield IExpression.i(n)

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(IIntLit(d))

    def augmentModelTermSet(model : Conjunction,
                            assignment : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = ()

    override def newConstant(name : String) : ConstantTerm =
      new ConstantTerm(name)
  }

  /**
   * The sort of natural numbers.
   */
  object Nat extends ProxySort(Interval(Some(IdealInt.ZERO), None)) {
    override val name : String = "nat"
  }

  /**
   * Sort representing (possibly left- or right-open) intervals.
   */
  case class Interval(lower : Option[IdealInt], upper : Option[IdealInt])
             extends Sort {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC,
                     (lower, upper) match {
                       case (Some(l), Some(u)) => l <= u
                       case _ => true
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val name : String =
      "int" +
      (lower match { case Some(l) => "[" + l
                     case None    => "(-infty" }) + ", " +
      (upper match { case Some(u) => "" + u + "]"
                     case None    => "infty)" })

    def membershipConstraint(t : ITerm) : IFormula = {
      import IExpression._
      (lower match { case Some(l) => t >= l
                     case None    => i(true) }) &&&
      (upper match { case Some(u) => t <= u
                     case None    => i(true) })
    }

    def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula = {
      val lcs =
        (lower match { case Some(l) => List(LinearCombination(
                                              Array((IdealInt.ONE, t),
                                                    (-l, OneTerm)), order))
                       case None    => List() }) ++
        (upper match { case Some(u) => List(LinearCombination(
                                              Array((IdealInt.MINUS_ONE, t),
                                                    (u, OneTerm)), order))
                       case None    => List() })
      InEqConj(lcs, order)
    }

    val cardinality =
      for (l <- lower; u <- upper) yield (u - l + 1)

    val individuals : Stream[ITerm] =
      (lower, upper) match {
        case (Some(l), Some(u)) =>
          for (n <- ap.util.IdealRange(l, u+1).toStream)
          yield IExpression.i(n)
        case (Some(l), None) =>
          for (n <- Stream.iterate(l){_ + 1})
          yield IExpression.i(n)
        case (None, Some(u)) =>
          for (n <- Stream.iterate(u){_ - 1})
          yield IExpression.i(n)
        case (None, None) =>
          Sort.Integer.individuals
      }

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(IIntLit(d))

    def augmentModelTermSet(model : Conjunction,
                            assignment : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = ()
  }

  //////////////////////////////////////////////////////////////////////////////
  // Uninterpreted sorts

  /**
   * Create a new uninterpreted sort of infinite cardinality.
   */
  def createInfUninterpretedSort(name : String) =
    UninterpretedSortTheory.createInfUninterpretedSort(name)
  
  /**
   * Create a new uninterpreted sort of finite or infinite cardinality.
   */
  def createUninterpretedSort(name : String) =
    UninterpretedSortTheory.createUninterpretedSort(name)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extractor to recognise sorts that are subsets of the integers.
   */
  object Numeric {
    def unapply(s : Sort) : Option[Sort] = s match {
      case Sort.Integer | Sort.Nat | _ : Sort.Interval => Some(s)
      case _ => None
    }
  }

  /**
   * Extractor to recognise non-numeric sorts.
   */
  object NonNumeric {
    def unapply(s : Sort) : Option[Sort] = s match {
      case Numeric(_) => None
      case s =>          Some(s)
    }
  }

  /**
   * The sort of Booleans. Booleans are encoded as an ADT with two
   * nullary constructors <code>true</code> (mapped to the integer
   * <code>0</code>), <code>false</code> (mapped to the integer
   * <code>1</code>).
   * @see ap.theories.ADT.BoolADT
   */
  lazy val Bool = ap.theories.ADT.BoolADT.boolSort

  /**
   * The sort of integers reinterpreted as Booleans. Integer <code>0</code.
   * is interpreted as <code>true</code>, every non-zero number as
   * <code>false</code>. For symbolic representation the same terms as in
   * sort <code>Bool</code> are used.
   * @see ap.theories.ADT.BoolADT
   * @see Bool
   */
  object MultipleValueBool extends ProxySort(Integer) {
    override val name : String = "MultipleValueBool"

    /**
     * Term representing the Boolean value <code>true</code>,
     * and mapped to integer <code>0</code>.
     */
    val True = ap.theories.ADT.BoolADT.True

    /**
     * Term representing the Boolean value <code>false</code>,
     * and mapped to integer <code>1</code>. (But note that every non-zero
     * number is interpreted as <code>false</code>).
     */
    val False = ap.theories.ADT.BoolADT.False

    /**
     * Construct a tester for <code>true</code>.
     */
    def isTrue(t : ITerm) : IFormula = IExpression.eqZero(t)

    /**
     * Construct a tester for <code>false</code>.
     */
    def isFalse(t : ITerm) : IFormula = !IExpression.eqZero(t)

    override val individuals : Stream[ITerm] =
      True #:: False #::
      (for (n <- Stream.iterate(IdealInt.MINUS_ONE){
                   n => if (n.signum <= 0) (-n+1) else -n
                 })
       yield IExpression.i(n))

    override def decodeToTerm(
                   d : IdealInt,
                   assign : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(if (d.isZero) True else False)

    override def augmentModelTermSet(
                   model : Conjunction,
                   assignment : MMap[(IdealInt, Sort), ITerm],
                   allTerms : Set[(IdealInt, Sort)],
                   definedTerms : MSet[(IdealInt, Sort)]) : Unit = {}
  }

  /**
   * A placeholder sort that is used in places where the sort has not been
   * inferred yet.
   */
  val AnySort = new ProxySort(Sort.Integer) {
    override val name = "any"
  }

  /**
   * Extractor to recognise sorts that represent the Booleans.
   */
  object AnyBool {
    def unapply(s : Sort) : Option[Sort] = s match {
      case Bool | MultipleValueBool => Some(s)
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extractor to identify terms with associated sort. This can be used for
   * checks like <code>t match { case t ::: Sort.Bool => XXX }</code>.
   */
  object ::: {
    def unapply(t : ITerm) : Option[(ITerm, Sort)] = Some((t, sortOf(t)))
  }

  /**
   * Determine the sort of the given term.
   */
  def sortOf(t : ITerm) : Sort = t match {
    case IConstant(c : SortedConstantTerm) =>
      c.sort
    case IFunApp(f : SortedIFunction, args) =>
      f iResultSort args
    case ISortedVariable(_, sort) =>
      sort
    case ISortedEpsilon(sort, _) =>
      sort
    case ITermITE(_, left, right) => {
      val lSort = sortOf(left)
      val rSort = sortOf(right)
      if (lSort == rSort) lSort else Sort.Integer
    }
    case _ =>
      Sort.Integer
  }

  object NonNumericTerm {
    def unapply(t : ITerm) : Option[(ITerm, Sort)] = sortOf(t) match {
      case Numeric(_) => None
      case sort       => Some((t, sort))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generate a stream of vectors of individuals in the given sort vector.
   */
  def individualsVectors(sorts : List[Sort]) : Stream[List[ITerm]] =
    sorts match {
      case List() =>
        Stream(List())
      case s :: sTail =>
        for (ind <- s.individuals; v <- individualsVectors(sTail))
        yield (ind :: v)
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Trait representing sorts of individuals in the logic.
 */
trait Sort {
  val name : String

  /**
   * Constraints defining the range of the sort.
   */
  def membershipConstraint(t : ITerm) : IFormula

  /**
   * Constraints defining the range of the sort.
   */
  def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula

  /**
   * The cardinality of sorts with fixed-size, finite domain.
   */
  val cardinality : Option[IdealInt]

  /**
   * A witness term proving that the sort is inhabited.
   */
  def witness : Option[ITerm] = individuals.headOption

  /**
   * Terms representing elements of the sort.
   */
  def individuals : Stream[ITerm]

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = name

  /**
   * Allocation of a new constant with <code>this</code> sort.
   */
  def newConstant(name : String) : ConstantTerm =
    new SortedConstantTerm(name, this)

  /**
   * The variable with given de Bruijn index and <code>this</code> sort.
   */
  def boundVariable(index : Int) : IVariable =
    ISortedVariable(index, this)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extract a term representation of some value in the sort.
   */
  val asTerm = new Theory.Decoder[Option[ITerm]] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext) : Option[ITerm] =
      (ctxt getDataFor TypeTheory) match {
        case TypeTheory.DecoderData(transl) => decodeToTerm(d, transl)
      }
  }

  /**
   * Extract a term representation of some value in the sort. This method
   * can be overwritten in sub-classes to decode in a sort-specific way
   */
  def decodeToTerm(d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
    assignment get ((d, this))

  /**
   * Extract terms from a model. Such terms will always be encoded as
   * integers, and integers can have different meaning depending on the
   * considered sort.
   */
  def augmentModelTermSet(model : Conjunction,
                          assignment : MMap[(IdealInt, Sort), ITerm],
                          allTerms : Set[(IdealInt, Sort)],
                          definedTerms : MSet[(IdealInt, Sort)]) : Unit

  protected def getSubTerms(ids : Seq[Term],
                            sorts : Seq[Sort],
                            terms : MMap[(IdealInt, Sort), ITerm])
                           : Either[Seq[ITerm], Seq[(IdealInt, Sort)]] = {
    val subTerms : Seq[Either[ITerm, (IdealInt, Sort)]] =
      for ((idTerm, sort) <- ids zip sorts) yield {
        val id = idTerm match {
          case idTerm : LinearCombination if idTerm.isConstant =>
            idTerm.constant
          case _ =>
            throw new IllegalArgumentException
        }

        sort.decodeToTerm(id, terms) match {
          case Some(t) => Left(t)
          case None    => Right((id, sort))
        }
      }

    if (subTerms forall (_.isLeft))
      Left(subTerms map (_.left.get))
    else
      Right(for (Right(key) <- subTerms) yield key)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def ex(f : IFormula) =
    ISortedQuantified(IExpression.Quantifier.EX, this, f)
  
  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def all(f : IFormula) =
    ISortedQuantified(IExpression.Quantifier.ALL, this, f)

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.ex(a => phi(a))</code>.
   */
  def ex(f : ITerm => IFormula) = {
    import IExpression._
    val x = newConstant("x")
    quanConsts(Quantifier.EX, List(x), f(x))
  }

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.ex((a, b) => phi(a, b))</code>.
   */
  def ex(f : (ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    quanConsts(Quantifier.EX, List(x1, x2), f(x1, x2))
  }

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.ex((a, b, c) => phi(a, b, c))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    quanConsts(Quantifier.EX, List(x1, x2, x3), f(x1, x2, x3))
  }

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.ex((a, b, c, d) => phi(a, b, c, d))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    val x4 = newConstant("x4")
    quanConsts(Quantifier.EX, List(x1, x2, x3, x4), f(x1, x2, x3, x4))
  }

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.ex((a, b, c, d, e) => phi(a, b, c, d, e))</code>.
   */
  def ex(f : (ITerm, ITerm, ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    val x4 = newConstant("x4")
    val x5 = newConstant("x5")
    quanConsts(Quantifier.EX, List(x1, x2, x3, x4, x5), f(x1, x2, x3, x4, x5))
  }

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.all(a => phi(a))</code>.
   */
  def all(f : ITerm => IFormula) = {
    import IExpression._
    val x = newConstant("x")
    quanConsts(Quantifier.ALL, List(x), f(x))
  }

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.all((a, b) => phi(a, b))</code>.
   */
  def all(f : (ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    quanConsts(Quantifier.ALL, List(x1, x2), f(x1, x2))
  }

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.all((a, b, c) => phi(a, b, c))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    quanConsts(Quantifier.ALL, List(x1, x2, x3), f(x1, x2, x3))
  }

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.all((a, b, c, d) => phi(a, b, c, d))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    val x4 = newConstant("x4")
    quanConsts(Quantifier.ALL, List(x1, x2, x3, x4), f(x1, x2, x3, x4))
  }

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as
   * <code>Sort.all((a, b, c, d, e) => phi(a, b, c, d, e))</code>.
   */
  def all(f : (ITerm, ITerm, ITerm, ITerm, ITerm) => IFormula) = {
    import IExpression._
    val x1 = newConstant("x1")
    val x2 = newConstant("x2")
    val x3 = newConstant("x3")
    val x4 = newConstant("x4")
    val x5 = newConstant("x5")
    quanConsts(Quantifier.ALL, List(x1, x2, x3, x4, x5), f(x1, x2, x3, x4, x5))
  }

  /**
   * Generate an epsilon-expression.
   */
  def eps(f : IFormula) =
    ISortedEpsilon(this, f)

  /**
   * Higher-order syntax for epsilon-expressions. This makes it possible
   * to write things like <code>Sort.eps(a => phi(a))</code>.
   */
  def eps(f : ITerm => IFormula) = {
    import IExpression._
    // first substitute a fresh constant, and later replace it with a
    // bound variable (just applying <code>f</code> to a bound variable
    // would not work in case of nested binders)
    val x = newConstant("x")
    val fWithShiftedVars = VariableShiftVisitor(f(x), 0, 1)
    ISortedEpsilon(this,
                   ConstantSubstVisitor(fWithShiftedVars, Map(x -> v(0, this))))
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to define proxy sorts, which inherit most properties from some
 * underlying sort, but may override some of the features.
 */
class ProxySort(underlying : Sort) extends Sort {
  val name : String = underlying.name

  def membershipConstraint(t : ITerm) : IFormula =
    underlying.membershipConstraint(t)

  def membershipConstraint(t : Term)(implicit order : TermOrder) : Formula =
    underlying.membershipConstraint(t)

  val cardinality : Option[IdealInt] = underlying.cardinality

  def individuals : Stream[ITerm] = underlying.individuals

  override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
    underlying.decodeToTerm(d, assignment)

  def augmentModelTermSet(model : Conjunction,
                          assignment : MMap[(IdealInt, Sort), ITerm],
                          allTerms : Set[(IdealInt, Sort)],
                          definedTerms : MSet[(IdealInt, Sort)]) : Unit =
    underlying.augmentModelTermSet(model, assignment, allTerms, definedTerms)
}

////////////////////////////////////////////////////////////////////////////////

object IntToTermTranslator {
  def apply(f : IFormula)
           (implicit decoderContext : Theory.DecoderContext) : IFormula = {
    val visitor = new IntToTermTranslator
    visitor.visit(f, ()).asInstanceOf[IFormula]
  }
}

/**
 * Class to systematically replace integer literals in an expression with
 * equivalent symbolic terms.
 */
class IntToTermTranslator(implicit decoderContext : Theory.DecoderContext)
      extends CollectingVisitor[Unit, IExpression] {
  import Sort.{NonNumericTerm, NonNumeric}
  import IExpression.{Sort => _, _}

  private def transformArgs(args : Seq[ITerm],
                            sorts : Seq[Sort]) : Seq[ITerm] = {
    var changed = false

    val newArgs =
      ((args.iterator zip sorts.iterator) map {
         case (d@IIntLit(value), NonNumeric(sort)) =>
           (sort asTerm value) match {
             case Some(t) => {
               changed = true
               t
             }
             case None =>
               d
           }
         case (arg, _) =>
           arg
       }).toVector

    if (changed) newArgs else args
  }

  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[IExpression]) : IExpression = {
    val nt = t update subres
    nt match {

      case IFunApp(f : SortedIFunction, args) => {
        val (argTypes, _) = f iFunctionType args
        val newArgs = transformArgs(args, argTypes)
        if (newArgs eq args) nt else IFunApp(f, newArgs)
      }

      case IAtom(p : SortedPredicate, args) => {
        val argTypes = p iArgumentSorts args
        val newArgs = transformArgs(args, argTypes)
        if (newArgs eq args) nt else IAtom(p, newArgs)
      }

      case Eq(NonNumericTerm(s, sSort), d@IIntLit(value)) =>
        (sSort asTerm value) match {
          case Some(sd) => s === sd
          case None => nt
        }

      case Eq(d@IIntLit(value), NonNumericTerm(s, sSort)) =>
        (sSort asTerm value) match {
          case Some(sd) => s === sd
          case None => nt
        }

      case _ =>
        nt
    }
  }
}
