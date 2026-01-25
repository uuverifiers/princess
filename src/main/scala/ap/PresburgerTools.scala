/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2026 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.basetypes.IdealInt
import ap.theories.{TheoryRegistry, ModuloArithmetic, TheoryCollector}
import ap.theories.GroebnerMultiplication
import ap.types.TypeTheory
import ap.proof.{ConstraintSimplifier, ModelSearchProver, ExhaustiveProver}
import ap.proof.theoryPlugins.PluginSequence
import ap.terfor.{Formula, ConstantTerm, VariableTerm, TermOrder, Term, OneTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               IterativeClauseMatcher, NegatedConjunctions,
                               SeqReducerPluginFactory}
import ap.terfor.preds.PredConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.{VariableShiftSubst, VariableSubst,
                                ConstantSubst}
import ap.terfor.TerForConvenience._
import ap.parameters.{GoalSettings, ReducerSettings, Param}
import ap.util.{Debug, Seqs, IdealRange, Combinatorics, Timeout}

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer}

/**
 * A collection of tools for analysing and transforming formulae in Presburger
 * arithmetic
 */
object PresburgerTools {

  private val AC = Debug.AC_PRESBURGER_TOOLS

  private val exhaustiveProver = new ExhaustiveProver (true, GoalSettings.DEFAULT)
  
  import Conjunction.{collectQuantifiers, conj, disj, negate, implies, quantify}
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isPresburger(f : Formula) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty
  
  def isQFPresburger(f : Formula) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty && collectQuantifiers(f).isEmpty
  
  def isExistentialPresburger(f : Formula) : Boolean =
    f.predicates.isEmpty && f.variables.isEmpty &&
    (collectQuantifiers(f) subsetOf Set(Quantifier.EX))
  
  def isQFPresburgerConjunction(f : Conjunction) : Boolean =
    isQFPresburger(f) &&
    !(f.negatedConjs exists ((c) => !c.isDivisibility && !c.isNonDivisibility))
  
  def containsBVNonlin(f : Formula) : Boolean =
    f.predicates exists {
      p => (TheoryRegistry lookupSymbol p) match {
        case Some(ModuloArithmetic)       => true
        case Some(GroebnerMultiplication) => true
        case _                            => false
      }
    }

  def containsTheories(f : Formula) : Boolean =
    !(f.predicates forall { p => (TheoryRegistry lookupSymbol p).isEmpty })

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Turn a formula into DNF. The DNF might not be complete in the sense that
   * a formula <code> a & b | a & c </code> might only be normalised to
   * <code> a & (b | c) </code>
   */
  def toDNF(formula : Conjunction) : Conjunction =
    if (isQFPresburger(formula))
      ConstraintSimplifier.LEMMA_SIMPLIFIER(formula, formula.order)
    else
      Conjunction.disj(toDNFGeneral(formula), formula.order)
  
  //////////////////////////////////////////////////////////////////////////////

  private def toDNFGeneral(f : Conjunction) : Seq[Conjunction] =
    if (f.isDivisibility || f.isNonDivisibility || f.isLiteral) {
      List(f)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, f.quans.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val order = f.order

      val subDNFs =
        (for (c <- f.negatedConjs) yield (toCNFGeneral(c) map (_.negate))).toList

      (for (combination <- Combinatorics.cartesianProduct(subDNFs))
       yield Conjunction.conj(combination.iterator ++
                              Seqs.doubleIterator(f.arithConj, f.predConj), order)).toSeq
    }

  private def toCNFGeneral(f : Conjunction) : Seq[Conjunction] =
    if (f.isDivisibility || f.isNonDivisibility || f.isLiteral) {
      List(f)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, f.quans.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val order = f.order

      (
        (for (a <- f.arithConj.iterator) yield Conjunction.conj(a, order)) ++
        (for (a <- f.predConj.iterator)  yield Conjunction.conj(a, order)) ++
        (for (c <- f.negatedConjs.iterator;
              disjunct <- toDNFGeneral(c).iterator) yield disjunct.negate)
      ).toSeq
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Enumerate the disjuncts of a formula that already is in DNF.
   */
  def enumDisjuncts(disjunction : Conjunction) : Iterator[Conjunction] =
    enumDisjunctsPos(disjunction, Conjunction.TRUE)
  
  /**
   * Enumerate the disjuncts of a formula (which might not be in DNF).
   */
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
            formula.negatedConjs.updateSubset(divisibilities, order)
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

  def isSatisfiable(rawFormula : Conjunction) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isPresburger(rawFormula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = ReduceWithConjunction(Conjunction.TRUE, rawFormula.order)(rawFormula)
    
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

  def isValid(rawFormula : Conjunction) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isPresburger(rawFormula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = ReduceWithConjunction(Conjunction.TRUE, rawFormula.order)(rawFormula)
    
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

  def hasCountermodel(rawFormula : Conjunction) : Option[Conjunction] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, isPresburger(rawFormula))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val formula = ReduceWithConjunction(Conjunction.TRUE, rawFormula.order)(rawFormula)
    
    if (formula.isTrue) {
      None
    } else if (formula.isFalse) {
      Some(Conjunction.TRUE)
    } else if (IterativeClauseMatcher.isMatchableRec(formula, Map())) {
      val model = ModelSearchProver(formula, formula.order)
      if (model.isFalse) None else Some(model)
    } else {
      // then we first have to eliminate quantifiers
      val qfFormula = elimQuantifiersWithPreds(formula)
      val model = ModelSearchProver(formula, formula.order)
      if (model.isFalse) None else Some(model)
    }
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
    implicit val order = constraint.order.extend(bound)
    
    val inEqLC = objective - LinearCombination(bound, order)
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

    if (boundSolutions.isTrue || boundSolutions.isFalse) {
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
    implicit val order = constraint.order.extend(List(lowerBound, upperBound))
    
    val lowerInEqLC = objective - LinearCombination(lowerBound, order)
    val upperInEqLC = LinearCombination(upperBound, order) - objective
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
   * formula. The method can also handle formulas with bit-vector arithmetic
   * or non-linear multiplication, and is optimised for post-processing of
   * interpolants.
   * 
   * TODO: revise, this is a messy implementation.
   */
  def elimQuantifiersWithPreds(c : Conjunction) : Conjunction = {
    implicit val order = c.order
    val signature = Signature(Set(), Set(), c.constants, order)
    val reducer =
      if (containsBVNonlin(c))
        ReduceWithConjunction(Conjunction.TRUE, order, bvReducerSettings)
      else
        ReduceWithConjunction(Conjunction.TRUE, order)
    val constraintSimplifier =
      ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF
    
    def simplifier(c : Conjunction, order : TermOrder) : Conjunction = {
      val quantifiers = Conjunction.collectQuantifiers(c)
      quantifiers.size match {
        case 0 =>
          c // nothing to do
        case 1 if c.predicates.isEmpty =>
          constraintSimplifier(c, order)
        case 2 if c.predicates.isEmpty =>
          expansionProver(c, order).closingConstraint
        case 1 if (quantifiers contains Quantifier.EX) => {
          // we need to add type constraints in general, otherwise QE might
          // give unexpected results
          val typedC = TypeTheory.preprocess(!c, signature)
          TypeTheory.filterTypeConstraints(
            !bvExpansionProver(typedC, order).closingConstraint)
        }
        case _ => {
          // we need to add type constraints in general, otherwise QE might
          // give unexpected results
          val typedC = TypeTheory.preprocess(c, signature)
          TypeTheory.filterTypeConstraints(
            bvExpansionProver(typedC, order).closingConstraint)
        }
      }
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
    def expandQuantifiers(c : Conjunction) : Conjunction = {
      Timeout.check

      c.quans.lastOption match {
        case (Some(Quantifier.EX)) => {
          val qvar = v(c.quans.size - 1)
          (c.arithConj.inEqs.findLowerBound(qvar),
           c.arithConj.inEqs.findLowerBound(-qvar)) match {
            case (Some(lb), Some(ub))
              // don't split if there would be more than 1000 cases
              // (hopeless ...)
              if (ub + lb > IdealInt(-1000)) =>
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
            case (Some(lb), Some(ub))
              // don't split if there would be more than 1000 cases
              // (hopeless ...)
              if (ub + lb > IdealInt(-1000)) =>
              conj(for (i <- IdealRange(lb, -ub + IdealInt.ONE).iterator)
                   yield expandQuantifiers(c.instantiate(List(i))), order)
            case _ =>
              c
          }
        }
        
        case _ =>
          c
      }
    }
    
    def quanElimPossible(c : Conjunction) : Boolean = c.predicates forall {
      p => (TheoryRegistry lookupSymbol p) match {
        case Some(ModuloArithmetic) =>
          p != ModuloArithmetic._bv_extract
        case _ =>
          false
      }
    }

    def elimHelp(c : Conjunction) : Conjunction =
      if (Conjunction.collectQuantifiers(c).isEmpty) {
        c // nothing to do
      } else {
          if (quanElimPossible(c)) {
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
                VariableSubst(0, freshConsts, extendedOrder)
              val consts2Vars =
                ConstantSubst(Map() ++ (for ((c, i) <- freshConsts.iterator.zipWithIndex)
                                          yield (c, VariableTerm(i))),
                              extendedOrder)
            
              consts2Vars(simplifier(vars2Consts(c), extendedOrder))
            }
            
          } else if (c.quans.isEmpty) {
            // nothing to eliminate
            
            descend(c)
            
          } else {
            val newC = miniScope(c)
            if (c == newC) {
              // then we cannot eliminate the quantifiers
              descend(expandQuantifiers(c))
            } else {
              elimHelp(newC)
            }
          }
      }

    elimHelp(reducer(c))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def miniScope(c : Conjunction) : Conjunction = {
    implicit val order = c.order
    
    if (c.size == 1 && c.negatedConjs.size == 1 && !c.quans.isEmpty) {
      !miniScope(quantify(for (q <- c.quans) yield q.dual, c.negatedConjs(0), order))
    } else {
      // first miniscope nested quantifiers
    
      val newNegConj =
        c.negatedConjs.update(for (d <- c.negatedConjs) yield miniScope(d), order)
      var newC =
        c.updateNegatedConjs(newNegConj)
    
      var cont = true
      while (cont) {
        cont = false
        
        if (!newC.quans.isEmpty) {
          val (with_0, without_0) =
            newC.iterator partition (_.variables contains VariableTerm._0)
          if (without_0.hasNext) {
            val shiftSubst = VariableShiftSubst(1, -1, order)
            
            val with_0_conj =
              miniScope(quantify(List(newC.quans.head), conj(with_0, order), order))
            val without_0_conj =
              conj(for (d <- without_0) yield shiftSubst(d), order)
              
            newC = quantify(newC.quans.tail, with_0_conj & without_0_conj, order)
            cont = true
          }
        }
      }
        
      newC
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val expansionSettings =
    Param.CONSTRAINT_SIMPLIFIER.set(GoalSettings.DEFAULT,
                                    ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF)
  private val expansionProver =
    new ExhaustiveProver(false, expansionSettings)

  // expansion in the presence of bit-vectors
  private val (bvReducerSettings, bvExpansionSettings) = {
    val collector =
      new TheoryCollector
    collector.addTheory(GroebnerMultiplication)
    collector.addTheory(ModuloArithmetic)
    val theories =
      collector.theories
    val functionalPreds =
      (for (t <- theories; p <- t.functionalPredicates) yield p).toSet
    val predicateMatchConfig =
      (for (t <- theories; p <- t.predicateMatchConfig) yield p).toMap

    val reducerSettings = {
      var rs = ReducerSettings.DEFAULT
      rs = Param.FUNCTIONAL_PREDICATES.set(
           rs, functionalPreds)
      rs = Param.REDUCER_PLUGIN.set(
           rs, SeqReducerPluginFactory
                 (for (t <- theories) yield t.reducerPlugin))
      rs
    }

    val expSettings = {
      var gs = GoalSettings.DEFAULT
      gs = Param.CONSTRAINT_SIMPLIFIER.set(gs,
                   ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF)
      gs = Param.REDUCER_SETTINGS.set(gs, reducerSettings)
      val plugin =
        PluginSequence(for (t <- theories; p <- t.plugin.toSeq) yield p)
      gs = Param.THEORY_PLUGIN.set(gs, plugin)
      gs = Param.FUNCTIONAL_PREDICATES.set(gs, functionalPreds)
      gs = Param.SINGLE_INSTANTIATION_PREDICATES.set(gs,
           (for (t <- theories.iterator;
                 p <- t.singleInstantiationPredicates.iterator) yield p).toSet)
      gs = Param.PREDICATE_MATCH_CONFIG.set(gs, predicateMatchConfig)
      gs
    }

    (reducerSettings, expSettings)
  }

  private val bvExpansionProver =
    new ExhaustiveProver(false, bvExpansionSettings)

  /**
   * Compute the most general quantifier-free formula without uninterpreted
   * predicates that implies the given formula, modulo the given axioms. If the
   * input formula or the axioms contain quantifiers, this might not terminate.
   */
  def eliminatePredicates(c : Conjunction, axioms : Conjunction,
                          order : TermOrder) : Conjunction = {
    implicit val o = order
    val fors = ReduceWithConjunction(Conjunction.TRUE, order)(!c | !axioms)
    expansionProver(fors, order).closingConstraint.negate
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Minimise the given formula by eliminating unnecessary disjuncts.
   * This is a stronger version of the simplification performed by
   * <code>ReduceWithConjunction</code>, and also simplifies formulae
   * <code>a & (b | c) & (b | c')</code> where <code>c & c'</code> is
   * unsatisfiable.
   */
  def minimiseFormula(c : Conjunction) : Conjunction = {
    val order = c.order
    val reducer = ReduceWithConjunction(Conjunction.TRUE, order)

    var newC = c
    var changed = true
    while (changed) {
      val newC2 = minimiseFormulaHelp(reducer(newC), reducer)
      changed = !(newC2 eq newC)
      newC = newC2
    }

    newC
  }

  private def minimiseFormulaHelp(
                  c : Conjunction,
                  reducer : ReduceWithConjunction) : Conjunction = {
    implicit val order = c.order
    val newNegatedConjs =
      c.negatedConjs.update(for (d <- c.negatedConjs)
                              yield minimiseFormulaHelp(d, reducer),
                            order)
    var newC =
      if (c.negatedConjs eq newNegatedConjs)
        c
      else
        reducer(c.updateNegatedConjs(newNegatedConjs))

    val impliedLiterals : Iterator[Conjunction] =
      if (newC.negatedConjs.size <= 1) {
        Iterator.empty
      } else {
        val checkedLits = new MHashSet[Conjunction]
        for (d <- newC.negatedConjs.iterator;
             lit <- d.iterator;
             if ({
                   if (checkedLits contains lit) {
                     false
                   } else {
                     checkedLits += lit
                     (ReduceWithConjunction(lit, order) tentativeReduce newC).isFalse
                   }
                 }))
        yield lit
      }

    if (impliedLiterals.hasNext)
      reducer(Conjunction.conj((for (lit <- impliedLiterals) yield !lit) ++
                                 (Iterator single newC),
                               order))
    else
      newC
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert a given formula to prenex form.
   * TODO: do something special for divisibilities?
   */
  def toPrenex(c : Conjunction) : Conjunction = {
    val subConj = (for (subC <- c.negatedConjs) yield toPrenex(subC)).toArray
    
    var currentQuan = c.quans.headOption.getOrElse(Quantifier.ALL)
    var allQuans = c.quans.toList
    
    while (subConj exists (!_.quans.isEmpty)) {
      currentQuan = currentQuan.dual
      
      val quanNums = for (d <- subConj)
        yield ((d.quans lastIndexOf currentQuan.dual) match {
          case -1 => d.quans.size
          case x => d.quans.size - x - 1
        })
            
      currentQuan match {
        case Quantifier.ALL => {
          val quanNum = quanNums.sum
          
          var innerOffset = 0
          for (i <- 0 until subConj.size) {
            val subst = VariableShiftSubst(Array.fill(quanNums(i)){innerOffset},
                                           quanNum - quanNums(i), c.order)
            subConj(i) = subst(subConj(i) unquantify quanNums(i))
            innerOffset = innerOffset + quanNums(i)
          }
          
          for (_ <- 0 until quanNum) allQuans = Quantifier.EX :: allQuans
        }
        case Quantifier.EX => {
          val quanNum = quanNums.max
          
          for (i <- 0 until subConj.size) {
            val subst = VariableShiftSubst(0, quanNum - quanNums(i), c.order)
            subConj(i) = subst(subConj(i)) unquantify quanNums(i)
          }
          
          for (_ <- 0 until quanNum) allQuans = Quantifier.ALL :: allQuans
        }
      }
    }

    val nShifter = VariableShiftSubst(0, allQuans.size - c.quans.size, c.order)
    
    Conjunction(allQuans,
                nShifter(c.arithConj),
                nShifter(c.predConj),
                NegatedConjunctions(subConj, c.order),
                c.order)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find an interpretation of the constants in the given terms that will make
   * all terms evaluate to pairwise distinct integers.
   */
  def distinctInterpretation[T <: Term](terms : Set[T], order : TermOrder)
                                      : Map[ConstantTerm, IdealInt] = {
    val suffixClosure = new MHashSet[LinearCombination]
    for (t <- terms) t match {
      case _ : ConstantTerm | OneTerm =>
        suffixClosure += LinearCombination(t, order)
      case lc : LinearCombination => {
        suffixClosure += lc
        val N = lc.size
        for (n <- 1 until N)
          suffixClosure += LinearCombination(lc.view(n, N), order)
      }
    }

    val suffixClosureSeq = suffixClosure.toIndexedSeq.sorted(order.lcOrdering)

    val assignment = new MHashMap[ConstantTerm, IdealInt]
    var curMin, curMax = IdealInt.ZERO
    val nextTerms = new ArrayBuffer[LinearCombination]

    def newValue(v : IdealInt) = {
      if (v < curMin)
        curMin = v
      else if (v > curMax)
        curMax = v
    }

    def eval(ts : Seq[(IdealInt, Term)]) : IdealInt =
      (for ((coeff, t) <- ts.iterator) yield t match {
         case OneTerm => coeff
         case c : ConstantTerm => coeff * assignment(c)
       }).sum

    var n = 0
    val N = suffixClosureSeq.size
    while (n < N)
      if (suffixClosureSeq(n).isConstant) {
        newValue(suffixClosureSeq(n).constant)
        n = n + 1
      } else {
        val nextConst =
          suffixClosureSeq(n).leadingTerm.asInstanceOf[ConstantTerm]
        nextTerms += suffixClosureSeq(n)
        n = n + 1
        
        while (n < N && suffixClosureSeq(n).leadingTerm == nextConst) {
          nextTerms += suffixClosureSeq(n)
          n = n + 1
        }

        nextTerms match {
          case Seq(Seq((IdealInt.ONE, c : ConstantTerm))) => {
            val v = curMax + IdealInt.ONE
            assignment.put(c, v)
            newValue(v)
          }

          case _ => {
            val tailVals =
              for (lc <- nextTerms) yield eval(lc.view(1, lc.size))

            var constV =
              (for ((lc, tailVal) <- nextTerms.iterator zip tailVals.iterator;
                    lCoeff = lc.leadingCoeff)
               yield lCoeff.signum match {
                 case 1  =>
                   (curMax - tailVal + (lCoeff - IdealInt.ONE)) / lCoeff
                 case -1 => -(curMin - tailVal)
               }).max + IdealInt.ONE

            assignment.put(nextConst, constV)

            val termValues =
              (for ((lc, tailVal) <- nextTerms.iterator zip tailVals.iterator)
               yield (tailVal + constV * lc.leadingCoeff)).toArray

            while (nextTerms.size > 1 &&
                   termValues.toSet.size < nextTerms.size) {
              constV = constV + IdealInt.ONE
              assignment.put(nextConst, constV)
              (for ((lc, tailVal) <- nextTerms.iterator zip tailVals.iterator)
               yield (tailVal + constV*lc.leadingCoeff)) copyToArray termValues
            }

            termValues foreach newValue
          }
        }

        nextTerms.clear
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC,
      (for (t <- terms.iterator)
       yield eval(LinearCombination(t, order))).toSet.size == terms.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    assignment.toMap
  }

}
