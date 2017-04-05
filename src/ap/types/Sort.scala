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

package ap.types

import ap.basetypes.IdealInt
import ap.parser._
import ap.terfor.{Term, Formula, TermOrder, OneTerm, ConstantTerm}
import ap.terfor.conjunctions.{Quantifier, Conjunction}
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.theories.Theory
import ap.util.Debug

import scala.collection.mutable.{HashMap => MHashMap}

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

    // TODO: remove witness field?

    def witness : Option[ITerm] = Some(IExpression.i(0))

    val individuals : Stream[ITerm] =
      for (n <- Stream.iterate(IdealInt.ZERO){
                  n => if (n.signum < 0) (-n+1) else -n
                })
      yield IExpression.i(n)

    def augmentModelTermSet(model : Conjunction,
                            terms : MHashMap[(IdealInt, Sort), ITerm])
                           : Unit = ()

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

    def witness : Option[ITerm] =
      (for (l <- lower) yield IExpression.i(l)) orElse
      (for (u <- upper) yield IExpression.i(u)) orElse
      Some(IExpression.i(0))

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

    def augmentModelTermSet(model : Conjunction,
                            terms : MHashMap[(IdealInt, Sort), ITerm])
                           : Unit = ()
  }

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
   * The sort of Booleans. Booleans are encoded as an ADT.
   * @see ap.theories.ADT.BoolADT
   */
  val Bool = ap.theories.ADT.BoolADT.boolSort

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extractor to identify terms with associated sort. This can be used for
   * checks like <code>t match { case t ::: Sort.Bool => XXX }</code>.
   */
  object ::: {
    def unapply(t : ITerm) : Option[(ITerm, Sort)] = t match {
      case IConstant(c : SortedConstantTerm) =>
        Some((t, c.sort))
      case IFunApp(f : SortedIFunction, args) =>
        Some((t, f iResultSort args))
      case t =>
        Some((t, Sort.Integer))
    }
  }

  object NonNumericTerm {
    def unapply(t : ITerm) : Option[(ITerm, Sort)] = t match {
      case IConstant(c : SortedConstantTerm) =>
        c.sort match {
          case Numeric(_) => None
          case sort =>       Some((t, sort))
        }
      case IFunApp(f : SortedIFunction, args) =>
        (f iResultSort args) match {
          case Numeric(_) => None
          case sort =>       Some((t, sort))
        }
      case t =>
        None
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
  def witness : Option[ITerm]

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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extract a term representation of some value in the sort.
   */
  val asTerm = new Theory.Decoder[Option[ITerm]] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext) : Option[ITerm] =
      (ctxt getDataFor TypeTheory) match {
        case TypeTheory.DecoderData(transl) => transl get ((d, Sort.this))
      }
  }

  /**
   * Extract terms from a model. Such terms will always be encoded as
   * integers, and integers can have different meaning depending on the
   * considered sort.
   */
  def augmentModelTermSet(model : Conjunction,
                          terms : MHashMap[(IdealInt, Sort), ITerm]) : Unit

  protected def getSubTerms(ids : Seq[Term],
                            sorts : Seq[Sort],
                            terms : MHashMap[(IdealInt, Sort), ITerm])
                           : Option[Seq[ITerm]] = {
    val subTerms =
      for ((idTerm, sort) <- ids zip sorts) yield {
        val id = idTerm match {
          case idTerm : LinearCombination if idTerm.isConstant =>
            idTerm.constant
          case _ =>
            throw new IllegalArgumentException
        }

        sort match {
          case Sort.Numeric(_) =>  IIntLit(id)
          case sort =>             terms.getOrElse((id, sort), null)
        }
      }

    if (subTerms contains null)
      None
    else
      Some(subTerms)
  }

  //////////////////////////////////////////////////////////////////////////////

  // TODO: the following methods should use SortedConstantTerm for the bound
  // symbol

  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def ex(f : IFormula) =
    IQuantified(Quantifier.EX,
                IExpression.guardEx(f, membershipConstraint(IVariable(0))))
  
  /**
   * Add an existential quantifier for the variable with de Bruijn index 0,
   * together with a guard representing this sort.
   */
  def all(f : IFormula) =
    IQuantified(Quantifier.ALL,
                IExpression.guardAll(f, membershipConstraint(IVariable(0))))

  /**
   * Higher-order syntax for existential quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.ex(a => phi(a))</code>.
   */
  def ex(f : ITerm => IFormula) =
    IExpression.ex(x => IExpression.guardEx(f(x), membershipConstraint(x)))

  /**
   * Higher-order syntax for universal quantifiers. This makes it possible
   * to write a quantifier as <code>Sort.all(a => phi(a))</code>.
   */
  def all(f : ITerm => IFormula) =
    IExpression.all(x => IExpression.guardAll(f(x), membershipConstraint(x)))

  /**
   * Generate an epsilon-expression.
   */
  def eps(f : IFormula) =
    IEpsilon(IExpression.guardEx(f, membershipConstraint(IExpression.v(0))))

  /**
   * Higher-order syntax for epsilon-expressions. This makes it possible
   * to write things like <code>Sort.eps(a => phi(a))</code>.
   */
  def eps(f : ITerm => IFormula) =
    IExpression.eps(x => IExpression.guardEx(f(x), membershipConstraint(x)))

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

  def witness : Option[ITerm] = underlying.witness

  def individuals : Stream[ITerm] = underlying.individuals

  def augmentModelTermSet(model : Conjunction,
                          terms : MHashMap[(IdealInt, Sort), ITerm]) : Unit =
    underlying.augmentModelTermSet(model, terms)
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
  import IExpression._
  import Sort.{NonNumericTerm, NonNumeric}

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
        val argTypes = p iArgumentTypes args
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