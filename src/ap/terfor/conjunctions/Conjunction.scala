/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import scala.collection.mutable.ArrayBuffer

import ap.basetypes.IdealInt
import ap.terfor._
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.{PredConj, Atom, Predicate}
import ap.terfor.substitutions.{IdentitySubst, VariableShiftSubst, Substitution,
                                ConstantSubst, VariableSubst}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Logic, Seqs, PlainRange}

object Conjunction {
  
  private val AC = Debug.AC_PROP_CONNECTIVES

  /**
   * Create a <code>Conjunction</code> from an arbitrary collection of formulas.
   * It is required that all given formulas are sorted by the specified
   * <code>order</code>.
   */
  def apply(quans : Seq[Quantifier],
            formulas : Iterator[Formula],
            logger : ComputationLogger,
            order : TermOrder) : Conjunction = {
    // first split up the input formulas into the arithmetic stuff and the
    // negated parts
    val (arithConj, predConj, negatedConjs) =
      segregateFormulas(formulas, logger, order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, !negatedConjs.containsLiteral &&
                        !negatedConjs.containsNegatedConjunction)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    createHelp(quans, arithConj, predConj, negatedConjs, order)
  }

  def apply(quans : Seq[Quantifier],
            formulas : Iterator[Formula],
            order : TermOrder) : Conjunction =
    apply(quans, formulas, ComputationLogger.NonLogger, order)

  /**
   * Take apart a list of conjuncts and create one arithmetic conjunction and
   * one conjunction of negated conjunctions
   */
  private def segregateFormulas(formulas : Iterator[Formula],
                                logger : ComputationLogger,
                                order : TermOrder)
                                : (ArithConj, PredConj, NegatedConjunctions) = {
    val arithFors = new ArrayBuffer[Formula]
    val predConjs = new ArrayBuffer[PredConj]
    val negConjs = new ArrayBuffer[Conjunction]
    
    def addNegatedConjunctions(negCs : NegatedConjunctions) : Unit =
      for (negC <- negCs) {
        if (negC.isLiteral) {
          val negAC = negC.arithConj
          val negPC = negC.predConj
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC,
                          (negAC.isLiteral != negPC.isLiteral) && negC.negatedConjs.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          if (negAC.isLiteral)
            arithFors += negAC.negate
          else
            predConjs += negPC.negate
        } else if (negC.isNegatedConjunction) {
          // remove double-negation
          addFormula(negC.negatedConjs(0))
        } else {
          negConjs += negC
        }
      }
    
    def addFormula(f : Formula) : Unit =
      if (!f.isTrue) {
        f match {
        case _ : EquationConj | _ : NegEquationConj | _ : InEqConj | _ : ArithConj =>
          arithFors += f
        case f : PredConj => predConjs += f
        case a : Atom => predConjs += PredConj(List(a), List(), order)
        case c : Conjunction =>
          if (c.quans.isEmpty) {
            arithFors += c.arithConj
            predConjs += c.predConj
            addNegatedConjunctions(c.negatedConjs)
          } else {
            // if the conjunction is quantified, negate it twice and then
            // add it
            addNegatedConjunctions(NegatedConjunctions(c.negate, order))
          }
        case negCs : NegatedConjunctions => addNegatedConjunctions(negCs)
        }
      }
    
    while (formulas.hasNext) {
      val f = formulas.next
      if (f.isFalse)
        return (ArithConj.FALSE, PredConj.TRUE, NegatedConjunctions.TRUE)
      addFormula(f)
    }
    
    (ArithConj.conj(arithFors.iterator, logger, order),
     PredConj.conj(predConjs.iterator, logger, order),
     NegatedConjunctions(negConjs, order))
  }
   
  def apply(quans : Seq[Quantifier],
            formulas : Iterable[Formula],
            order : TermOrder) : Conjunction =
    apply(quans, formulas.iterator, order)

  /**
   * Compute a conjunction from an arbitrary set of formulas
   */
  def conj(formulas : Iterator[Formula], order : TermOrder) : Conjunction =
    apply(List(), formulas, order)    

  def conj(formulas : Iterable[Formula], order : TermOrder) : Conjunction =
    apply(List(), formulas.iterator, order)  
    
  def conj(f : Formula, order : TermOrder) : Conjunction =
    apply(List(), Iterator.single(f), order)  
    
  /**
   * Compute a disjunction from an arbitrary set of formulas
   */
  def disjFor(formulas : Iterator[Formula], order : TermOrder) : Conjunction =
    conj(for (f <- formulas) yield conj(f, order).negate,
         order).negate

  def disj(formulas : Iterator[Conjunction], order : TermOrder) : Conjunction =
    conj(for (f <- formulas) yield f.negate, order).negate

  def disjFor(formulas : Iterable[Formula], order : TermOrder) : Conjunction =
    disjFor(formulas.iterator, order)

  def disj(formulas : Iterable[Conjunction], order : TermOrder) : Conjunction =
    disj(formulas.iterator, order)

  /**
   * Form the implication between two formulas
   */
  def implies(for1 : Formula, for2 : Formula, order : TermOrder) : Conjunction =
    disj(Array(negate(for1, order), conj(for2, order)), order)
    
  /**
   * Form the equivalence between two formulas
   */
  def eqv(for1 : Formula, for2 : Formula, order : TermOrder) : Conjunction =
//    disj(Array(conj(Array(for1, for2), order),
//               conj(Array(negate(for1, order), negate(for2, order)), order)),
//         order)
    conj(Array(implies(for1, for2, order), implies(for2, for1, order)), order)
    
  /**
   * Quantify a formula
   */
  def quantify(quans : Seq[Quantifier], f : Formula, order : TermOrder)
                                                                : Conjunction =
    apply(quans, Iterator.single(f), order)
    
  /**
   * Quantify a number of constants in a formula, i.e., replace the constants
   * with variables and add quantifiers
   */
  def quantify(quan : Quantifier, constants : Seq[ConstantTerm],
               f : Formula, order : TermOrder) : Conjunction = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // This is only well-defined if the formula does not contain free variables
    Debug.assertPre(AC, f.variables.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val constantSubst = ConstantSubst(Map() ++
                                      (for ((c, i) <- constants.iterator.zipWithIndex)
                                       yield (c -> VariableTerm(i))),
                                      order)
    val quans : Seq[Quantifier] =
      (for (_ <- PlainRange(constants.size)) yield quan)    
    
    quantify(quans, constantSubst(f), order)
  }
    
  /**
   * Negate a formula
   */
  def negate(f : Formula, order : TermOrder) : Conjunction =
    apply(List(), Iterator.single(f), order).negate
    
  /**
   * Create a <code>Conjunction</code> from an arbitrary collection of formulas.
   * It is required that all given formulas are sorted by the specified
   * <code>order</code>.
   */
  def apply(quans : Seq[Quantifier],
            arithConj : ArithConj,
            predConj : PredConj,
            negatedConjs : NegatedConjunctions,
            order : TermOrder) : Conjunction = {
    if (arithConj.isFalse || predConj.isFalse) {
      FALSE
    } else if (negatedConjs.containsLiteral ||
               negatedConjs.containsNegatedConjunction) {
      // go back to the more general method that first splits up the formulas
      // into the different parts
      apply(quans, Array(arithConj, predConj, negatedConjs), order)
    } else {
      createHelp(quans, arithConj, predConj, negatedConjs, order)
    }
  }

  private def createHelp(quans : Seq[Quantifier],
                         arithConj : ArithConj,
                         predConj : PredConj,
                         negatedConjs : NegatedConjunctions,
                         order : TermOrder) : Conjunction = {
    if (arithConj.isTrue && predConj.isTrue &&
        negatedConjs.isNegatedQuantifiedConjunction) {
      // pull out the quantifiers
      val negC = negatedConjs(0)
      apply((for (q <- negC.quans) yield q.dual) ++ quans,
            ArithConj.TRUE,
            PredConj.TRUE,
            NegatedConjunctions(createFromNormalised(List(),
                                                     negC.arithConj,
                                                     negC.predConj,
                                                     negC.negatedConjs,
                                                     order),
                                order),
            order)
     } else {
       createFromNormalised(quans, arithConj, predConj, negatedConjs, order)
     }
  }
   
  /**
   * Create a <code>Conjunction</code> from different parts that are already
   * normalised. This primarily means that <code>negatedConjs</code> must not
   * contain any conjunctions that are just literals, and that quantifiers are
   * pulled out completely if the conjunction only has a single conjunct.
   */
  def createFromNormalised(quans : Seq[Quantifier],
                           arithConj : ArithConj,
                           predConj : PredConj,
                           negatedConjs : NegatedConjunctions,
                           order : TermOrder) : Conjunction = {
    if (arithConj.isFalse || predConj.isFalse || negatedConjs.isFalse)
      FALSE
    else if (arithConj.isTrue && predConj.isTrue && negatedConjs.isTrue)
      TRUE
    else {
      val occurringVars = new scala.collection.mutable.HashSet[VariableTerm]
      occurringVars ++= arithConj.variables
      occurringVars ++= predConj.variables
      occurringVars ++= negatedConjs.variables
      val (resultingQuans, resultingSubst) =
        eliminateUnusedQuans(occurringVars, quans, order)
      
      new Conjunction (resultingQuans,
                       resultingSubst(arithConj),
                       resultingSubst(predConj),
                       resultingSubst(negatedConjs),
                       order)
    }
  }
  
  /**
   * Remove all quantifiers from <code>quans</code> that talk about variables
   * not occurring in <code>occurringVars</code>. The result is the filtered
   * sequence of quantifiers and a <code>Substitution</code> for adjusting the
   * remaing variables
   */
  private def eliminateUnusedQuans(occurringVars : scala.collection.Set[VariableTerm],
                                   quans : Seq[Quantifier],
                                   order : TermOrder)
                                          : (Seq[Quantifier], Substitution) =
    if ((0 until quans.size) forall (occurringVars contains VariableTerm(_))) {
      (quans, new IdentitySubst(order))
    } else {
      val resultingQuans = new ArrayBuffer[Quantifier]
      val variableShifts = new Array[Int] (quans.size)
      
      var usedVars : Int = 0
      for ((q, i) <- quans.iterator.zipWithIndex) {
        variableShifts(i) = usedVars - i
        if (occurringVars contains VariableTerm(i)) {
          usedVars = usedVars + 1
          resultingQuans += q
        }
      }

      var resultingSubst : Substitution =
        VariableShiftSubst(variableShifts, usedVars - quans.size, order)

      (resultingQuans, resultingSubst)
    }
   
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Determine the quantifiers that occur in a formula. Because there are 
   * different points of view, a function can be given as parameter that
   * determines whether (quantified) divisibility/indivisibility statements are
   * counted as quantifiers
   */
  def collectQuantifiers(f : Formula, divCollector : (Conjunction) => Set[Quantifier])
                                                  : Set[Quantifier] = f match {
    case f : Conjunction =>
      if (f.isQuantifiedDivisibility || f.isQuantifiedNonDivisibility)
        divCollector(f)
      else
        Set() ++ f.quans ++ collectQuantifiers(f.negatedConjs, divCollector)
    case conjs : NegatedConjunctions => {
      var res : Set[Quantifier] = Set()
      for (conj <- conjs) {
        res = res ++ (for (q <- collectQuantifiers(conj, divCollector)) yield q.dual)
        if (res.size == 2) return res // at most two quantifiers ...
      }
      res
    }
    case _ => Set()
  }

  /**
   * Default: divisibility is not counted (but we count immediately preceeding
   * quantifiers)
   */
  def collectQuantifiers(f : Formula) : Set[Quantifier] =
    collectQuantifiers(f, (conj) => Set() ++ conj.quans.drop(1))

  //////////////////////////////////////////////////////////////////////////////
   
  val TRUE : Conjunction =
    new Conjunction (List(), ArithConj.TRUE, PredConj.TRUE, NegatedConjunctions.TRUE, TermOrder.EMPTY)
  
  val FALSE : Conjunction =
    new Conjunction (List(), ArithConj.FALSE, PredConj.TRUE, NegatedConjunctions.TRUE, TermOrder.EMPTY)
                                            
}

/**
 * Class for representing (possibly quantified) conjunctions of arithmetic
 * literal (equations, inequalities), predicate literals and negated
 * <code>Conjunction</code>s. <code>quans</code> describes how the lowest
 * <code>quans.size</code> variables are quantified in the conjunction 
 * (<code>quans(0)</code>) is responsible for <code>VariableTerm(0)</code> and
 * is the innermost quantifier, etc).
 */
class Conjunction private (val quans : Seq[Quantifier],
                           val arithConj : ArithConj,
                           val predConj : PredConj,
                           val negatedConjs : NegatedConjunctions,
                           val order : TermOrder)
                  extends Formula with SortedWithOrder[Conjunction] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Conjunction.AC,
                   (arithConj isSortedBy order) &&
                   (predConj isSortedBy order) &&
                   (negatedConjs isSortedBy order) &&
                   // if the conjunction of negated conjunctions would have to
                   // be false, the arithmetic conjunction is set to false
                   // instead
                   (!arithConj.isFalse || predConj.isTrue && negatedConjs.isEmpty) &&
                   !negatedConjs.isFalse && !predConj.isFalse &&
                   // simple literals in the set of negated conjunctions can be
                   // normalised away
                   !negatedConjs.containsLiteral &&
                   // there must be no double-negations
                   !negatedConjs.containsNegatedConjunction &&
                   // there must not be any unused quantifiers
                   Logic.forall(0, quans.size,
                                (i) => variablesUnderQuans contains VariableTerm(i)) &&
                   // we do not want nested quantifiers through nested
                   // conjunctions; in this case, the quantifiers should be
                   // pulled out to the top-level
                   !(arithConj.isTrue && predConj.isTrue && negatedConjs.size == 1 &&
                     !negatedConjs(0).quans.isEmpty))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : Conjunction = {
    if (isSortedBy(newOrder)) {
      this
    } else {
      // TODO: can the reordering possibly break the class invariants?
      Conjunction.createFromNormalised (quans,
                                        arithConj sortBy newOrder,
                                        predConj sortBy newOrder,
                                        negatedConjs sortBy newOrder,
                                        newOrder)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private lazy val variablesUnderQuans : Set[VariableTerm] =
    arithConj.variables ++ predConj.variables ++ negatedConjs.variables

  lazy val boundVariables : Set[VariableTerm] =
    Set() ++ (for (i <- 0 until quans.size) yield VariableTerm(i))
  
  lazy val variables : Set[VariableTerm] =
    for (VariableTerm(i) <- variablesUnderQuans; if (i >= quans.size))
    yield VariableTerm(i - quans.size)

  lazy val constants : Set[ConstantTerm] =
    arithConj.constants ++ predConj.constants ++ negatedConjs.constants

  lazy val predicates : Set[Predicate] =
    arithConj.predicates ++ predConj.predicates ++ negatedConjs.predicates

  lazy val groundAtoms : Set[Atom] =
    arithConj.groundAtoms ++ predConj.groundAtoms ++ negatedConjs.groundAtoms

  //////////////////////////////////////////////////////////////////////////////

  def isTrue : Boolean = (arithConj.isTrue && predConj.isTrue && negatedConjs.isTrue)

  /**
   * The only allow case of false is when <code>arithConj</code> is false and
   * everything else is empty.
   */
  def isFalse : Boolean = arithConj.isFalse

  def size : Int = arithConj.size + predConj.size + negatedConjs.size
  
  def iterator : Iterator[Conjunction] =
    (for (c <- arithConj.iterator)
       yield Conjunction.conj(c, order)) ++
    (for (atom <- predConj.iterator)
       yield Conjunction.conj(atom, order)) ++
    (for (c <- negatedConjs.iterator) yield c.negate)
  
  /**
   * Return whether this conjunction actually only is a single literal
   * (a single, unquantified (in)equation, inequality or predicate literal)
   */
  def isLiteral : Boolean =
    (quans.isEmpty && negatedConjs.isEmpty &&
     (arithConj.isLiteral && predConj.isTrue ||
      arithConj.isTrue && predConj.isLiteral))
  
  /**
   * Return whether this conjunction actually only is a single arithmetic 
   * literal (a single, unquantified (in)equation, inequality)
   */
  def isArithLiteral : Boolean =
    (quans.isEmpty && negatedConjs.isEmpty &&
     arithConj.isLiteral && predConj.isTrue)

  //////////////////////////////////////////////////////////////////////////////
    
  /**
   * Return whether <code>this</code> is a divisibility judgement
   * <code>EX (n*_0 + t = 0)</code>
   */
  def isDivisibility : Boolean = {
    val res = (quans sameElements List(Quantifier.EX)) && isDivisibilityHelp
	              
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Conjunction.AC,
         res == (!arithConj.positiveEqs.isEmpty &&
                 (arithConj.positiveEqs(0).variables contains VariableTerm._0) && 
                 this == Conjunction.quantify(List(Quantifier.EX),
                                              EquationConj(arithConj.positiveEqs(0),
                                                           order),
                                              order)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
      
    res
  }

  /**
   * Return whether <code>this</code> is a divisibility judgement
   * <code>EX (n*_0 + t = 0)</code>, possibly underneath quantifiers
   */
  def isQuantifiedDivisibility : Boolean = {
    val res = (quans startsWith List(Quantifier.EX)) && isDivisibilityHelp
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Conjunction.AC,
                     res == this.unquantify(quans.size - 1).isDivisibility)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
   
  // Test whether the matrix of the conjunction could belong to a divisibility
  private def isDivisibilityHelp : Boolean =
    (arithConj.positiveEqs.size == 1) &&
    (arithConj.size == 1) &&
    predConj.isTrue && negatedConjs.isEmpty
    
   
  /**
   * Return whether <code>this</code> is a negated divisibility judgement
   * <code>ALL (n*_0 + t != 0)</code>
   */
  def isNonDivisibility : Boolean = {
    val res = (quans sameElements List(Quantifier.ALL)) && isNonDivisibilityHelp
                 
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Conjunction.AC,
         res == (!arithConj.negativeEqs.isEmpty &&
                 (arithConj.negativeEqs(0).variables contains VariableTerm._0) && 
                 this == Conjunction.quantify(List(Quantifier.ALL),
                                              NegEquationConj(arithConj.negativeEqs(0),
                                                              order),
                                              order)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
       
    res
  }

  /**
   * Return whether <code>this</code> is a negated divisibility judgement
   * <code>ALL (n*_0 + t != 0)</code>, possibly underneath quantifiers
   */
  def isQuantifiedNonDivisibility : Boolean = {
    val res = (quans startsWith List(Quantifier.ALL)) && isNonDivisibilityHelp
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Conjunction.AC,
                     res == this.unquantify(quans.size - 1).isNonDivisibility)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
    
  // Test whether the matrix of the conjunction could belong to a negated divisibility
  private def isNonDivisibilityHelp : Boolean =
    (arithConj.negativeEqs.size == 1) &&
    (arithConj.size == 1) &&
    predConj.isTrue && negatedConjs.isEmpty

  /**
   * Assuming that this formula is a divisibility or non-divisibility statement,
   * check whether the divisibility is proper (i.e., not of the form
   * <code>ALL (1*_0 + t != 0)</code>)
   */
  def isProperDivisibility : Boolean = {
    val lc = (arithConj.positiveEqs.iterator ++
              arithConj.negativeEqs.iterator).next.leadingCoeff
    !lc.isOne
  }
    
  //////////////////////////////////////////////////////////////////////////////
  // Tests to recognise guarded quantifiers
  // Such quantifiers can be handled very efficiently in proofs, since
  // Skolemisation can be applied, regardless of the sign and kind of the
  // quantifier
  
  /**
   * "Division quantifiers" of the form
   *    <code> EX ( n*_0 + t >= 0 & -n*_0 - t - m >= 0 & phi ) </code>
   * where <code> 0 <= m < n </code>.
   * 
   * The result of this test is a triple
   * <code>(n*_0 + t, -n*_0 - t - m, phi)</code>,
   * or <code>None</code> if the formula is not of the guarded quantifier shape
   */
  def isDivisionFormula
      : Option[(LinearCombination, LinearCombination, Conjunction)] =
    if (quans.size == 1) isQuantifiedDivisionFormula else None
  
  def isQuantifiedDivisionFormula
      : Option[(LinearCombination, LinearCombination, Conjunction)] =
    if (!quans.isEmpty && quans.head == Quantifier.EX) {
      for ((lowerBound, upperBound, remInEqs) <- isDivisionFormulaHelp) yield {
        val phi = Conjunction(List(),
                              arithConj.updateInEqs(remInEqs)(order),
                              predConj, negatedConjs, order)
        (lowerBound, upperBound, phi)
      }
    } else {
      None
    }
  
  def isDivisionFormulaHelp
      : Option[(LinearCombination, LinearCombination, InEqConj)] = {
    val inEqs = arithConj.inEqs
    
    var i = 0
    while (i < inEqs.size && inEqs(i).leadingTerm == VariableTerm._0) {
      val lc = inEqs(i)
      val n = lc.leadingCoeff
      if (n.signum > 0) {
        val negLC = -lc
        (inEqs findLowerBound negLC) match {
          case Some(negDistance) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(Conjunction.AC, negDistance.signum < 0)
            //-END-ASSERTION-///////////////////////////////////////////////////
            val distance = -negDistance
            if (distance < n) {
              // we found the guard, now take apart the formula
              // into the guard expressions and the body
              val (guards, otherInEqs) = inEqs partition {
                case `lc` => true
                case l if (l sameNonConstantTerms negLC) => true
                case _ => false
              }
              
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(Conjunction.AC, guards.size == 2 && guards(0) == lc)
              //-END-ASSERTION-/////////////////////////////////////////////////

              return Some(lc, guards(1),
                          inEqs.updateGeqZeroSubset(otherInEqs)(order))
            }
          }
          case _ => // nothing
        }
      }
    }
    
    None
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  
  /**
   * "Exact division quantifiers" of the form
   *    <code> EX ( n*_0 + t = 0 & phi) </code>
   * where <code> 0 < n </code>.
   * 
   * The result of this test is a pair
   * <code>(n*_0 + t, phi)</code>,
   * or <code>None</code> if the formula is not of the guarded quantifier shape
   */
  def isExactDivisionFormula
      : Option[(LinearCombination, Conjunction)] =
    if (quans.size == 1) isQuantifiedExactDivisionFormula else None
  
  def isQuantifiedExactDivisionFormula
      : Option[(LinearCombination, Conjunction)] =
    if (!quans.isEmpty && quans.head == Quantifier.EX) {
      for ((eq, remEqs) <- isExactDivisionFormulaHelp) yield {
        val phi = Conjunction(List(),
                              arithConj.updatePositiveEqs(remEqs)(order),
                              predConj, negatedConjs, order)
        (eq, phi)
      }
    } else {
      None
    }
  
  def isExactDivisionFormulaHelp : Option[(LinearCombination, EquationConj)] = {
    val eqs = arithConj.positiveEqs
    
    if (!eqs.isEmpty && eqs.head.leadingTerm == VariableTerm._0) {
      val lc = eqs.head
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(Conjunction.AC, lc.leadingCoeff.signum > 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val otherEqs = eqs.updateEqsSubset(eqs.tail)(order)
      
      Some(lc, otherEqs)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(Conjunction.AC, !(eqs.variables contains VariableTerm._0))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      None
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def negate : Conjunction =
    Conjunction(List(), ArithConj.TRUE, PredConj.TRUE,
                NegatedConjunctions(this, order), order)
    
  def unary_! : Conjunction = this.negate
  
  def &(that : Conjunction)(implicit newOrder : TermOrder) : Conjunction =
    Conjunction.conj(Array(this, that), newOrder)
  
  def |(that : Conjunction)(implicit newOrder : TermOrder) : Conjunction =
    Conjunction.disj(Array(this, that), newOrder)

  def ==>(that : Conjunction)(implicit newOrder : TermOrder) : Conjunction =
    Conjunction.implies(this, that, newOrder)

  def <=>(that : Conjunction)(implicit newOrder : TermOrder) : Conjunction =
    Conjunction.eqv(this, that, newOrder)

  /**
   * Remove the <code>num</code> outermost quantifiers of this
   * <code>Conjunction</code>, without changing the matrix of the formula
   */
  def unquantify(num : Int) : Conjunction =
    Conjunction.createFromNormalised(quans.take(quans.size - num),
                                     arithConj, predConj, negatedConjs, order)
  
  /**
   * Instantiate the outermost quantifiers with the given terms, starting with
   * the innermost quantifier to be instantiated
   */
  def instantiate(terms : Seq[Term])(implicit newOrder : TermOrder) : Conjunction =
    new VariableSubst (0, terms, newOrder) (unquantify(terms.size))
  
  /**
   * Update the arithmetic parts of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateArithConj(ac : ArithConj)(implicit newOrder : TermOrder) : Conjunction =
    if (arithConj == ac)
      this
    else
      Conjunction(quans, ac, predConj, negatedConjs, newOrder)

  /**
   * Update the predicate parts of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updatePredConj(pc : PredConj)(implicit newOrder : TermOrder) : Conjunction =
    if (predConj == pc)
      this
    else
      Conjunction(quans, arithConj, pc, negatedConjs, newOrder)

  /**
   * Update the positive equations of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updatePositiveEqs(newEqs : EquationConj)(implicit newOrder : TermOrder)
                       : Conjunction =
    updateArithConj(arithConj updatePositiveEqs newEqs)

  /**
   * Update the negative equations of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateNegativeEqs(newEqs : NegEquationConj)(implicit newOrder : TermOrder)
                       : Conjunction =
    updateArithConj(arithConj updateNegativeEqs newEqs)

  /**
   * Update the inequalities of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateInEqs(newEqs : InEqConj)(implicit newOrder : TermOrder) : Conjunction =
    updateArithConj(arithConj updateInEqs newEqs)

  /**
   * Update the inequalities of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateNegatedConjs(newNegConjs : NegatedConjunctions)(implicit newOrder : TermOrder)
                        : Conjunction =
    if (newNegConjs == this.negatedConjs)
      this
    else
      Conjunction(quans, arithConj, predConj, newNegConjs, newOrder)

  /**
   * Return whether this conjunction actually is the negation of a single
   * conjunction
   */
  def isNegatedConjunction : Boolean =
    (isPurelyNegated && negatedConjs.size == 1)

  /**
   * Return whether this conjunction only contains negated sub-conjunctions
   */
  def isPurelyNegated : Boolean =
    (quans.isEmpty && arithConj.isTrue && predConj.isTrue)
    
  //////////////////////////////////////////////////////////////////////////////

  def implies(that : Conjunction) : Boolean =
    // TODO: make this more efficient
    (this.quans sameElements that.quans) &&
    (this.arithConj implies that.arithConj) &&
    (this.predConj implies that.predConj) &&
    (this.negatedConjs implies that.negatedConjs)
   
  //////////////////////////////////////////////////////////////////////////////

  override def equals(that : Any) : Boolean = that match {
    case that : Conjunction => (this eq that) ||
                               this.hashCodeVal == that.hashCodeVal &&
                               (this.quans sameElements that.quans) &&
                               this.arithConj == that.arithConj &&
                               this.predConj == that.predConj &&
                               this.negatedConjs == that.negatedConjs
    case _ => false
  }
  
  private lazy val hashCodeVal =
    Seqs.computeHashCode(this.quans, 982473, 3) +
    arithConj.hashCode + predConj.hashCode + negatedConjs.hashCode

  override def hashCode = hashCodeVal
  
  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val quanPrefix = ("" /: quans)((p, q) => "" + q + " " + p)      
      val strings = for (f <- List(arithConj, predConj, negatedConjs); if (!f.isTrue))
                    yield f.toString
      
      quanPrefix +
        "(" + strings.reduceLeft((s1 : String, s2 : String) => s1 + " & " + s2) + ")"
    }
  }

}
