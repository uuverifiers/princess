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

package ap

import ap.basetypes.IdealInt
import ap.proof.{ConstraintSimplifier, ModelSearchProver, ExhaustiveProver}
import ap.terfor.{Formula, ConstantTerm, VariableTerm, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction}
import ap.terfor.preds.PredConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.{VariableShiftSubst, VariableSubst, ConstantSubst}
import ap.terfor.TerForConvenience._
import ap.parameters.{GoalSettings, Param}
import ap.util.{Debug, Seqs, IdealRange}

/**
 * A collection of tools for analysing and transforming formulae in Presburger
 * arithmetic
 */
object PresburgerTools {

  private val AC = Debug.AC_PRESBURGER_TOOLS

  private val exhaustiveProver = new ExhaustiveProver (true, GoalSettings.DEFAULT)
  
  import Conjunction.{collectQuantifiers, conj, disj, negate, implies, quantify}
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isPresburger(f : Conjunction) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty
  
  def isQFPresburger(f : Conjunction) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty && collectQuantifiers(f).isEmpty
  
  def isExistentialPresburger(f : Conjunction) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty &&
    (collectQuantifiers(f) subsetOf Set(Quantifier.EX))
  
  def isQFPresburgerConjunction(f : Conjunction) : Boolean =
    isQFPresburger(f) &&
    !(f.negatedConjs exists ((c) => !c.isDivisibility && !c.isNonDivisibility))
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Turn a formula into DNF. The DNF might not be complete in the sense that
   * a formula <code> a & b | a & c </code> might only be normalised to
   * <code> a & (b | c) </code>
   */
  def toDNF(formula : Conjunction) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isQFPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    ConstraintSimplifier.LEMMA_SIMPLIFIER(formula, formula.order)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def enumDisjuncts(disjunction : Conjunction) : Iterator[Conjunction] =
    enumDisjunctsPos(disjunction, Conjunction.TRUE)
  
  def nonDNFEnumDisjuncts(formula : Conjunction) : Iterator[Conjunction] =
    enumDisjuncts(toDNF(formula))
  
  private def enumDisjunctsPos(formula : Conjunction,
                               conjuncts : Conjunction) : Iterator[Conjunction] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isQFPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val order = formula.order
    def returnAll = Iterator.single(conj(Array(conjuncts, formula), order))

    if (formula.quans.isEmpty) {
      val (divisibilities, realNegConjs) =
        formula.negatedConjs partition ((c) => c.isDivisibility || c.isNonDivisibility)
      realNegConjs match {
        // because we assume that the given formula is in DNF, other cases
        // should not occur
        case Seq() => returnAll
        case Seq(disjunction) => {
          val divisibilitiesNegConj =
            formula.negatedConjs.update(divisibilities, order)
          val newConjuncts =
            conj(Array(conjuncts,
                       formula.updateNegatedConjs(divisibilitiesNegConj)(order)),
                 order)
          enumDisjunctsNeg(disjunction, newConjuncts)
        }
      }
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, formula.isDivisibility || formula.isNonDivisibility)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      returnAll
    }
  }

  private def enumDisjunctsNeg(formula : Conjunction,
                               conjuncts : Conjunction) : Iterator[Conjunction] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isQFPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (formula.quans.isEmpty) {
      (for (c <- formula.arithConj.iterator)
         yield conj(Array(conjuncts, c.negate), formula.order)) ++
      (for (c <- formula.negatedConjs.iterator;
            d <- enumDisjunctsPos(c, conjuncts)) yield d)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, formula.isDivisibility || formula.isNonDivisibility)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      Iterator.single(conj(Array(conjuncts, formula.negate), formula.order))
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def isSatisfiable(formula : Conjunction) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (formula.isTrue)
      true
    else if (formula.isFalse)
      false
    else if (isQFPresburger(formula))
      !ModelSearchProver(formula.negate, formula.order).isFalse
    else
      exhaustiveProver(Conjunction.quantify(Quantifier.EX,
                                            formula.order sort formula.constants,
                                            formula, formula.order),
                       formula.order).closingConstraint.isTrue
  }

  def isValid(formula : Conjunction) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (formula.isTrue)
      true
    else if (formula.isFalse)
      false
    else if (isQFPresburger(formula))
      ModelSearchProver(formula, formula.order).isFalse
    else
      exhaustiveProver(Conjunction.quantify(Quantifier.ALL,
                                            formula.order sort formula.constants,
                                            formula, formula.order),
                       formula.order).closingConstraint.isTrue
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Enumerate the models of a given formula. Currently, we assume that the
   * formula does not contain predicates and only existential quantifiers
   * (this could be relaxed)
   */
  def enumModels(formula : Conjunction) : Iterator[Conjunction] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isExistentialPresburger(formula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    new Iterator[Conjunction] {
      private val order = formula.order
      private var currentFormula = formula.negate
      private var nextModel : Conjunction = null
      
      private def computeModel = {
        if (nextModel == null) {
          nextModel = ModelSearchProver(currentFormula, order)
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // Currently, we just assume that the model will describe the values
          // of all variables (otherwise, there are infinitely many models,
          // but of course we might also want to enumerate those)
          Debug.assertInt(AC,
                          nextModel.isFalse || nextModel.constants == formula.constants)
          //-END-ASSERTION-/////////////////////////////////////////////////////
        }
      }
      
      def hasNext : Boolean = {
        computeModel
        !nextModel.isFalse
      }
      
      def next : Conjunction = {
        computeModel
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, !nextModel.isFalse)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val res = nextModel
        
        nextModel = null
        currentFormula = disj(Array(currentFormula, res), order)
          
        res
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether the function <code>objective</code> has a lower bound
   * subject to <code>constraint</code>, and return such a bound.
   */
  def lowerBound(objective : LinearCombination,
                 constraint : Conjunction) : Option[IdealInt] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (objective isSortedBy constraint.order) &&
                        isQFPresburger(constraint))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val bound = new ConstantTerm ("bound")
    val order = constraint.order.extend(bound, Set())
    
    val inEqLC = LinearCombination(Array((IdealInt.ONE, objective),
                                         (IdealInt.MINUS_ONE, bound)),
                                   order)
    val boundInEq = InEqConj(inEqLC, order)
    val imp = implies(constraint, boundInEq, order)
    val quantifiedImp = quantify(Quantifier.ALL,
                                 order.sort(constraint.constants ++ objective.constants),
                                 imp, order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, quantifiedImp.constants == Set(bound))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val boundSolutions =
      ReduceWithConjunction(Conjunction.TRUE, order)(
        ConstraintSimplifier.LEMMA_SIMPLIFIER(quantifiedImp, order))

    if (boundSolutions.isFalse) {
      // there are no bounds
      None
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC,
                      boundSolutions.isLiteral &&
                      !boundSolutions.arithConj.inEqs.isTrue &&
                      boundSolutions.arithConj.inEqs(0).leadingTerm == bound &&
                      boundSolutions.arithConj.inEqs(0).leadingCoeff.isMinusOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      Some(boundSolutions.arithConj.inEqs(0).constant)
    }
  }
  
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether the function <code>objective</code> has both a lower and an
   * upper bound subject to <code>constraint</code>, and return such bounds.
   */
  def bounds(objective : LinearCombination,
             constraint : Conjunction) : Option[(IdealInt, IdealInt)] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, (objective isSortedBy constraint.order) &&
                        isQFPresburger(constraint))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val lowerBound = new ConstantTerm ("lowerBound")
    val upperBound = new ConstantTerm ("upperBound")
    val order = constraint.order.extend(lowerBound, Set()).extend(upperBound, Set())
    
    val lowerInEqLC = LinearCombination(Array((IdealInt.ONE, objective),
                                              (IdealInt.MINUS_ONE, lowerBound)),
                                        order)
    val upperInEqLC = LinearCombination(Array((IdealInt.MINUS_ONE, objective),
                                              (IdealInt.ONE, upperBound)),
                                        order)
    val boundInEqs = InEqConj(Array(lowerInEqLC, upperInEqLC), order)
    val imp = implies(constraint, boundInEqs, order)
    val quantifiedImp = quantify(Quantifier.ALL,
                                 order sort (constraint.constants ++ objective.constants),
                                 imp, order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, quantifiedImp.constants == Set(lowerBound, upperBound))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val boundSolutions =
      ReduceWithConjunction(Conjunction.TRUE, order)(
        ConstraintSimplifier.LEMMA_SIMPLIFIER(quantifiedImp, order))

    if (boundSolutions.isFalse) {
      // there are no bounds
      None
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC,
                      boundSolutions.arithConj.positiveEqs.isEmpty &&
                      boundSolutions.arithConj.negativeEqs.isEmpty &&
                      boundSolutions.negatedConjs.isEmpty &&
                      boundSolutions.arithConj.inEqs.size == 2 &&
                      boundSolutions.arithConj.inEqs(0).leadingTerm == upperBound &&
                      boundSolutions.arithConj.inEqs(0).leadingCoeff.isOne &&
                      boundSolutions.arithConj.inEqs(1).leadingTerm == lowerBound &&
                      boundSolutions.arithConj.inEqs(1).leadingCoeff.isMinusOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      Some(boundSolutions.arithConj.inEqs(1).constant,
           -boundSolutions.arithConj.inEqs(0).constant)
    }
  }
  
  /**
   * Quantifier elimination procedure that can also handle uninterpreted
   * predicates, provided that predicates never occur in the scope of
   * quantifiers. Quantifiers above predicate occurrences are left in the
   * formula. The formula <code>c</code> must not contain both universal
   * and existential quantifiers, only one kind is allowed.
   */
  def elimQuantifiersWithPreds(c : Conjunction) : Conjunction = {
    implicit val order = c.order
    val reducer = ReduceWithConjunction(Conjunction.TRUE, order)
    val constraintSimplifier = ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF
    
    def simplifier(c : Conjunction, order : TermOrder) : Conjunction =
      Conjunction.collectQuantifiers(c).size match {
        case 0 => c // nothing to do
        case 1 => constraintSimplifier(c, order)
        case 2 => expansionProver(c, order).closingConstraint
      }
   
    def descend(c : Conjunction) : Conjunction = {
      val newNegatedConjs =
        c.negatedConjs.update(for (d <- c.negatedConjs) yield elimHelp(d),
                              order)
      reducer(c.updateNegatedConjs(newNegatedConjs)(order))
    }
    
    /**
     * Simple heuristic to expand quantifiers ranging over bounded domains
     */
    def expandQuantifiers(c : Conjunction) : Conjunction = c.quans.lastOption match {
      case (Some(Quantifier.EX)) => {
        val qvar = v(c.quans.size - 1)
        (c.arithConj.inEqs.findLowerBound(qvar),
         c.arithConj.inEqs.findLowerBound(-qvar)) match {
          case (Some(lb), Some(ub)) =>
            disj(for (i <- IdealRange(lb, -ub + IdealInt.ONE).iterator)
                 yield expandQuantifiers(c.instantiate(List(i))), order)
          case _ =>
            c
        }
      }
      
      case (Some(Quantifier.ALL))
        if (c.arithConj.isTrue && c.predConj.isTrue && c.negatedConjs.size == 1) => {
        val qvar = v(c.quans.size - 1)
        val subC = c.negatedConjs.head
        
        (subC.arithConj.inEqs.findLowerBound(qvar),
         subC.arithConj.inEqs.findLowerBound(-qvar)) match {
          case (Some(lb), Some(ub)) =>
            conj(for (i <- IdealRange(lb, -ub + IdealInt.ONE).iterator)
                 yield expandQuantifiers(c.instantiate(List(i))), order)
          case _ =>
            c
        }
      }
        
      case _ =>
        c
    }
    
    def elimHelp(c : Conjunction) : Conjunction =
      if (Conjunction.collectQuantifiers(c).isEmpty) {
        c // nothing to do
      } else {
          if (c.predicates.isEmpty) {
            // just call the quantifier eliminator
        
            if (c.variables.isEmpty) {
              simplifier(c, order)
            } else {
              // if the formula contains variables, we have to replace them with
              // fresh constants to be able to call the simplifier
              
              val maxVar =
                Seqs.max(for (VariableTerm(i) <- c.variables) yield i)
              val freshConsts =
                Array.tabulate(maxVar + 1)((i:Int) => new ConstantTerm("x"))
            
              val extendedOrder = order extend freshConsts
              
              val vars2Consts =
                new VariableSubst(0, freshConsts, extendedOrder)
              val consts2Vars =
                ConstantSubst(Map() ++ (for ((c, i) <- freshConsts.iterator.zipWithIndex)
                                          yield (c, VariableTerm(i))),
                              extendedOrder)
            
              consts2Vars(simplifier(vars2Consts(c), extendedOrder))
            }
            
          } else if (c.quans.isEmpty) {
            // nothing to eliminate
            
            descend(c)
            
          } else if (Seqs.disjoint(c.predConj.variables, c.boundVariables) &&
                     (c.negatedConjs forall
                        ((d : Conjunction) => Seqs.disjoint(d.variables, c.boundVariables) ||
                                              d.predicates.isEmpty))) {
            // It is possible to miniscope and remove all predicates from underneath
            // the quantifier
              
            val (withoutPreds, withPreds) = c.negatedConjs partition (_.predicates.isEmpty)
            val newC = Conjunction(c.quans, c.arithConj, PredConj.TRUE,
                                   c.negatedConjs.update(withoutPreds, order),
                                   order)
            
            // take care of other variables in the remaining parts
            val shifter = VariableShiftSubst.downShifter[Conjunction](c.quans.size, order)
            reducer(elimHelp(newC) &
                    shifter(c.predConj & c.negatedConjs.update(withPreds, order)))
            
          } else {
            // then we cannot eliminate the quantifiers
            
            descend(expandQuantifiers(c))
            
          }

      }
      
    elimHelp(reducer(c))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val expansionSettings =
    Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT,
                                    ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF)
  private val expansionProver =
    new ExhaustiveProver(false, expansionSettings)

  /**
   * Compute the most general quantifier-free formula without uninterpreted
   * predicates that implies the given formula, modulo the given axioms. If the
   * input formula or the axioms contain quantifiers, this might not terminate.
   */
  def eliminatePredicates(c : Conjunction, axioms : Conjunction,
                          order : TermOrder) : Conjunction = {
    implicit val o = order
    val fors = !c | !axioms
    expansionProver(fors, order).closingConstraint.negate
  }
}
