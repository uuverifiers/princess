/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.certificates

import ap.basetypes.IdealInt
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.substitutions.ConstantSubst
import ap.util.Debug

/**
 * Abstract superclass of all certificate nodes that only have a single subtree
 */
abstract class CertificateOneChild(val child : Certificate)
               extends Certificate {

  lazy val localProvidedFormulas : Seq[Set[Conjunction]] =
    List(uniqueLocalProvidedFormulas)

  protected val uniqueLocalProvidedFormulas : Set[Conjunction]

  //////////////////////////////////////////////////////////////////////////////

  def length = 1
  def apply(i : Int) : Certificate = {
    if (i != 0)
      throw new NoSuchElementException
    child
  }
  def iterator = Iterator single child

}

////////////////////////////////////////////////////////////////////////////////

object BranchInferenceCertificate {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inferences that do not cause proof splitting and that do not close a branch
 * are collected in nodes of this class.
 */
case class BranchInferenceCertificate(inferences : Seq[BranchInference],
                                      _child : Certificate,
                                      order : TermOrder) extends {

  private val providedAssumed : (Set[Conjunction], Set[Conjunction]) =
    ((Set[Conjunction](), Set[Conjunction]()) /: inferences) {
      case ((provided, assumed), inf) =>
        (provided ++ inf.providedFormulas,
         assumed ++ (inf.assumedFormulas -- provided))
    }

  val uniqueLocalProvidedFormulas : Set[Conjunction] = providedAssumed _1
  val localAssumedFormulas : Set[Conjunction] = providedAssumed _2

  val closingConstraint =
    (inferences :\ _child.closingConstraint)(_ propagateConstraint _)
  
} with CertificateOneChild(_child) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(BranchInferenceCertificate.AC,
                   uniqueLocalProvidedFormulas forall (_ isSortedBy child.order))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  override def toString : String =
    "BranchInferences(" + (inferences mkString ", ") + ", " + child + ")"
  
  override def inferenceCount : Int = super.inferenceCount - 1 + inferences.size

}

////////////////////////////////////////////////////////////////////////////////

object BranchInference { 
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Abstract superclass of all inferences that do not cause proof splitting and
 * that do not close proof branches
 */
abstract class BranchInference {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(BranchInference.AC,
                   (assumedFormulas forall ((c:Conjunction) => !c.isTrue)) &&
                   !(providedFormulas forall ((c:Conjunction) => c.isTrue)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  val assumedFormulas : Set[Conjunction]
  
  /**
   * Formulae that are introduced into the antecedent by this rule application.
   * This will implicitly simplify formulae (all
   * simplifications that are built into the datastructures are carried out).
   */
  val providedFormulas : Set[Conjunction]

  /**
   * Define the modification imposed by this rule application on the closing
   * constraint.
   */
  def propagateConstraint(closingConstraint : Conjunction) : Conjunction
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Inference corresponding to an application of alpha rules.
 */
case class AlphaInference(splitFormula : Conjunction,
                          providedFormulas : Set[Conjunction]) extends {
  
  val assumedFormulas = Set[Conjunction](splitFormula)
  
} with BranchInference {
  
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint

  override def toString : String =
    "Alpha(" + splitFormula + " -> " + (providedFormulas mkString ", ") + ")"
}

////////////////////////////////////////////////////////////////////////////////

object QuantifierInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to applications of the rules <code>all-left</code>,
 * <code>ex-left</code>, etc. A uniform prefix of quantifiers (only forall or
 * only exists) is instantiated with a single inference.
 * <code>newConstants</code> are the constants introduced to instantiate the
 * quantifiers, starting with the innermost instantiated quantifier.
 */
case class QuantifierInference(quantifiedFormula : Conjunction,
                               newConstants : Seq[ConstantTerm],
                               result : Conjunction,
                               order : TermOrder)
           extends {

  val assumedFormulas = Set(quantifiedFormula)
  val providedFormulas = Set(result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(QuantifierInference.AC,
                   !newConstants.isEmpty &&
                   {
                     val quans = quantifiedFormula.quans
                     !quans.isEmpty &&
                     // the instantiate quantifiers are uniform
                     (quans.drop(quans.size - newConstants.size) forall
                                                          (quans.last == _)) &&
                     // and no quantifiers of the same kind are left
                     (quans.size == newConstants.size ||
                      quans(quans.size - newConstants.size - 1) != quans.last)
                   } &&
                   result == quantifiedFormula.instantiate(newConstants)(order))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def propagateConstraint(closingConstraint : Conjunction) = {
    implicit val o = order
    quantify(quantifiedFormula.quans.last.dual, newConstants, closingConstraint)
  }

  override def toString : String =
    "Quantifier((" + quantifiedFormula + ") [" +
    (newConstants mkString ", ") + "] -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object GroundInstInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to applications of the rules <code>all-left</code>,
 * <code>ex-left</code>, etc. A uniform prefix of quantifiers (only forall or
 * only exists) is instantiated with a single inference.
 * <code>newConstants</code> are the constants introduced to instantiate the
 * quantifiers, starting with the innermost instantiated quantifier.
 */
case class GroundInstInference(quantifiedFormula : Conjunction,
                               instanceTerms : Seq[LinearCombination],
                               result : Conjunction,
                               order : TermOrder)
           extends {

  val assumedFormulas = Set(quantifiedFormula)
  val providedFormulas = Set(result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(GroundInstInference.AC,
                   !instanceTerms.isEmpty &&
                   (instanceTerms forall (_.variables.isEmpty)) &&
                   {
                     val quans = quantifiedFormula.quans
                     !quans.isEmpty &&
                     // the instantiate quantifiers are universal
                     (quans.drop(quans.size - instanceTerms.size) forall
                                                          (Quantifier.ALL == _)) &&
                     // and no quantifiers of the same kind are left
                     (quans.size == instanceTerms.size ||
                      quans(quans.size - instanceTerms.size - 1) != quans.last)
                   } &&
                   result == quantifiedFormula.instantiate(instanceTerms)(order))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint

  override def toString : String =
    "GroundInst((" + quantifiedFormula + ") [" +
    (instanceTerms mkString ", ") + "] -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object ReduceInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to a series of applications of the reduce rule to a
 * negated equation or an inequality (reduction of positive equalities is
 * described using <code>CombineEquationsInference</code>).
 */
case class ReduceInference(equations : Seq[(IdealInt, EquationConj)],
                           targetLit : ArithConj, result : ArithConj,
                           order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](targetLit) ++
                             (for ((_, e) <- equations.iterator) yield eqConj2Conj(e))
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ReduceInference.AC,
                   targetLit.isLiteral && targetLit.positiveEqs.isTrue &&
                   !equations.size.isEmpty &&
                   result == {
                     implicit val o = order
                     val modifier =
                       sum(for ((c, e) <- equations.iterator) yield (c, e(0)))
                     val ArithConj(_, negEqs, inEqs) = targetLit
                     ArithConj(EquationConj.TRUE,
                               negEqs +++ modifier =/= 0, inEqs +++ modifier >= 0,
                               order)
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint  

  /**
   * The left-hand side of the resulting inequality or negated equation, before
   * any simplification steps
   */
  lazy val unsimplifiedLHS : LinearCombination = {
    implicit val o = order
    val ArithConj(_, negEqs, inEqs) = targetLit
    val oriLHS = if (negEqs.isTrue) inEqs(0) else negEqs(0)
    val modifier = sum(for ((c, e) <- equations.iterator) yield (c, e(0)))
    oriLHS + modifier
  }

  override def toString : String =
    "Reduce(" + targetLit + " + " +
    ((for ((c, e) <- equations) yield "" + c + " * (" + e + ")") mkString " + ") +
    " -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object ReducePredInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to a series of applications of the reduce rule to the
 * arguments of a predicate literal. This is essentially the same as the
 * <code>ReduceInference</code>, only that all of the arguments can be reduced
 * simultaneously
 */
case class ReducePredInference(equations : Seq[Seq[(IdealInt, EquationConj)]],
                               targetLit : PredConj, result : PredConj,
                               order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](targetLit) ++
                             (for (eqs <- equations.iterator;
                                   (_, e) <- eqs.iterator) yield eqConj2Conj(e))
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ReducePredInference.AC,
                   targetLit.isLiteral && result.isLiteral &&
                   targetLit.positiveLits.isEmpty == result.positiveLits.isEmpty &&
                   targetLit.predicates == result.predicates &&
                   targetLit.predicates.size == 1 &&
                   targetLit.predicates.iterator.next.arity == equations.size &&
                   (equations exists (!_.isEmpty)) &&
                   result == {
                     implicit val o = order
                     val targetAtom = if (targetLit.positiveLits.isEmpty)
                                        targetLit.negativeLits(0)
                                      else
                                        targetLit.positiveLits(0)
                     
                     val newArgs =
                       for ((lc, eqs) <- targetAtom.iterator zip equations.iterator)
                       yield (lc + sum(for ((c, e) <- eqs.iterator) yield (c, e(0))))
                     
                     val newAtom = targetAtom.pred(newArgs)
                     if (targetLit.positiveLits.isEmpty)
                       !atom2PredConj(newAtom)
                     else
                       atom2PredConj(newAtom)
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint  

  override def toString : String =
    "ReducePred(" + targetLit + " + (" +
    ((for (eqs <- equations) yield
      ((for ((c, e) <- eqs) yield "" + c + " * (" + e + ")") mkString " + "))
     mkString ", ") +
    ") -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object CombineEquationsInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to a series of applications of the reduce rule: form
 * the linear combination of a sequence of equations. The result is implicitly
 * made primitive (divided by common coefficients)
 */
case class CombineEquationsInference(equations : Seq[(IdealInt, EquationConj)],
                                     result : EquationConj,
                                     order : TermOrder)
           extends {

  val assumedFormulas =
    Set() ++ (for ((_, e) <- equations.iterator) yield eqConj2Conj(e))
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(CombineEquationsInference.AC,
                   // no interesting inferences can be made from only one
                   // equation
                   equations.size >= 2 &&
                   (equations forall { case (c, e) => !c.isZero && e.size == 1 }) &&
                   !result.isTrue &&
                   (result.isFalse || result.size == 1) &&
                   result == { implicit val o = order; unsimplifiedLHS === 0 })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint

  /**
   * The left-hand side of the resulting equation, before
   * any simplification steps
   */
  lazy val unsimplifiedLHS : LinearCombination = {
    implicit val o = order
    sum(for ((c, e) <- equations.iterator) yield (c, e(0)))
  }

  override def toString : String =
    "CombineEquations(" +
    ((for ((c, e) <- equations) yield "" + c + " * (" + e + ")") mkString " + ") +
    " -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object ColumnReduceInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to an application of the <code>col-red</code> or
 * <code>col-red-subst</code> rule. This will simply introduce a new constant
 * <code>newSymbol</code> that is defined by <code>definingEquation</code>.
 */
case class ColumnReduceInference(oldSymbol : ConstantTerm, newSymbol : ConstantTerm,
                                 definingEquation : EquationConj,
                                 subst : Boolean, order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction]()
  val providedFormulas = Set[Conjunction](definingEquation)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ColumnReduceInference.AC,
                   definingEquation.size == 1 && !definingEquation.isFalse &&
                   (definingEquation(0) get (oldSymbol)).abs.isOne &&
                   (definingEquation(0) get (newSymbol)) ==
                     -(definingEquation(0) get (oldSymbol)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private lazy val constraintSubst = {
    implicit val o = order
    ConstantSubst(newSymbol,
                  newSymbol - definingEquation(0) * (definingEquation(0) get (newSymbol)),
                  order)
  }
  
  def propagateConstraint(closingConstraint : Conjunction) = {
    implicit val o = order
    if (subst)
      constraintSubst(closingConstraint)
    else
      forall(newSymbol, closingConstraint)
  }

  override def toString : String =
    "ColumnReduce(" + oldSymbol + " -> " + newSymbol + ", " + definingEquation + ")"
}

////////////////////////////////////////////////////////////////////////////////

object CombineInequalitiesInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Inference corresponding to a series of applications of the reduce rule: form
 * the linear combination of a sequence of equations. The result is implicitly
 * made primitive (divided by common coefficients) and rounded
 */
case class CombineInequalitiesInference(leftCoeff : IdealInt, leftInEq : InEqConj,
                                        rightCoeff : IdealInt, rightInEq : InEqConj,
                                        result : InEqConj,
                                        order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](leftInEq, rightInEq)
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(CombineInequalitiesInference.AC,
                   leftInEq.size == 1 && rightInEq.size == 1 &&
                   !leftInEq.isFalse && !rightInEq.isFalse &&
                   leftCoeff.signum > 0 && rightCoeff.signum > 0 &&
                   !result.isTrue &&
                   (result.isFalse || result.size == 1) &&
                   result == { implicit val o = order; unsimplifiedLHS >= 0})
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint

  /**
   * The left-hand side of the resulting equation, before
   * any simplification steps
   */
  lazy val unsimplifiedLHS : LinearCombination = {
    implicit val o = order
    leftInEq(0) * leftCoeff + rightInEq(0) * rightCoeff
  }

  override def toString : String =
    "CombineInequalities(" +
    leftCoeff + " * (" + leftInEq + ") + " + rightCoeff + " * (" + rightInEq +
    ") -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object AntiSymmetryInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Turn two complementary inequalities into an equation
 */
case class AntiSymmetryInference(leftInEq : InEqConj, rightInEq : InEqConj,
                                 result : EquationConj, order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](leftInEq, rightInEq)
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AntiSymmetryInference.AC,
                   leftInEq.size == 1 && rightInEq.size == 1 &&
                   !leftInEq.isFalse && !rightInEq.isFalse &&
                   result.size == 1 && !result.isFalse &&
                   leftInEq(0) == -rightInEq(0) &&
                   result == {
                     implicit val o = order
                     leftInEq(0) === 0
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint
  
  override def toString : String =
    "AntiSymmetry((" + leftInEq + "), (" + rightInEq + ") -> " + result + ")"
}

////////////////////////////////////////////////////////////////////////////////

object DirectStrengthenInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * Given the two formulae <code>t >= 0</code> and <code>t != 0</code> (or,
 * similarly, <code>t >= 0</code> and <code>-t != 0</code>), infer
 * the inequality <code>t-1 >= 0</code>. This kind of inference exists as a
 * separate rule to keep certificates more compact.
 */
case class DirectStrengthenInference(inequality : InEqConj, equation : NegEquationConj,
                                     result : InEqConj, order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](inequality, equation)
  val providedFormulas = Set[Conjunction](result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(DirectStrengthenInference.AC,
                   inequality.size == 1 && !inequality.isFalse &&
                   equation.size == 1 && !equation.isFalse &&
                   result.size == 1 && !result.isFalse &&
                   (Set(equation(0), -equation(0)) contains inequality(0)) &&
                   result == {
                     implicit val o = order
                     inequality(0) > 0
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint
  
  override def toString : String =
    "DirectStrengthen((" + inequality + "), (" + equation + ") -> " + result + ")"
}


////////////////////////////////////////////////////////////////////////////////

object DivRightInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * An inference that turns a universally quantified divisibility constraint into
 * an existentially quantified conjunction of inequalities and an equation.
 */
case class DivRightInference(divisibility : Conjunction,
                             result : Conjunction, order : TermOrder)
           extends {

  val assumedFormulas = Set(divisibility)
  val providedFormulas = Set(result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(DivRightInference.AC,
                   divisibility.isNonDivisibility && {
                      implicit val o = order
                      val divTerm = divisibility.arithConj.negativeEqs(0)
                      val divCoeff = (divTerm(0) _1)
                      
                      result == exists(exists(
                        (divTerm + v(1) === 0) & (v(1) > 0) & (v(1) < divCoeff)))
                    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint
  
  override def toString : String =
    "DivRight(" + divisibility +" -> " + result + ")"
}


////////////////////////////////////////////////////////////////////////////////

object PredUnifyInference {
  private val AC = Debug.AC_CERTIFICATES
}

/**
 * An inference describing the unification of two predicates, producing a
 * system of equations (in the succedent) that express the unification
 * conditions: the predicate arguments are matched pair-wise
 */
case class PredUnifyInference(leftAtom : Atom, rightAtom : Atom,
                              result : EquationConj, order : TermOrder)
           extends {

  val assumedFormulas = Set[Conjunction](PredConj(List(leftAtom), List(), order),
                                         PredConj(List(), List(rightAtom), order))
  val providedFormulas = Set[Conjunction](!result)

} with BranchInference {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(PredUnifyInference.AC, {
                     implicit val o = order
                     leftAtom.pred == rightAtom.pred &&
                     result ==
                       ((for ((l, r) <- leftAtom.iterator zip rightAtom.iterator)
                           yield (l - r)).toList === 0)
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
             
  def propagateConstraint(closingConstraint : Conjunction) = closingConstraint
  
  override def toString : String =
    "PredUnify(" + leftAtom + ", " + rightAtom +" -> " + result + ")"
}
