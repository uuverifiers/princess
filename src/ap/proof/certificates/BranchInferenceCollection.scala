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
import ap.terfor.conjunctions.Conjunction
import ap.terfor.arithconj.ArithConj
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.equations.EquationConj
import ap.terfor.ComputationLogger
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet}

object BranchInferenceCollection {
  
  val EMPTY = new BranchInferenceCollection(List())

  def apply(initialFors : Iterable[Conjunction]) : BranchInferenceCollection =
    if (initialFors.isEmpty)
      EMPTY
    else
      apply((for (f <- initialFors; inf <- genAlphaInferences(f)) yield inf).toList)
  
  def apply(inferences : List[BranchInference]) =
    new BranchInferenceCollection(inferences)
  
  /**
   * Generate applications of the alpha rule to the given conjunction
   */
  private[certificates] def genAlphaInferences(f : Conjunction) : Seq[BranchInference] =
    if (f.size > 1)
      List(AlphaInference(f, Set() ++ f.elements))
    else
      List()
}

/**
 * Class to store sets of branch inferences in goals. Currently, the inferences
 * are just kept in a list, but this might change at a late point. This is an
 * immutable datastructure, for dynamically collecting inferences use
 * <code>BranchInferenceCollector</code>.
 */
class BranchInferenceCollection private (val inferences : List[BranchInference]) {

  def getCollector : BranchInferenceCollector =
    LoggingBranchInferenceCollector(inferences)
  
  def getCertificate(child : Certificate, order : TermOrder) : Certificate =
    if (inferences.isEmpty) {
      child
    } else {
      val requiredFormulas = new MHashSet[Conjunction]
      requiredFormulas ++= child.assumedFormulas
    
      var selectedInferences : List[BranchInference] = List()
    
      for (inf <- inferences)
        if (!Seqs.disjoint(inf.providedFormulas, requiredFormulas)) {
          requiredFormulas --= inf.providedFormulas
          requiredFormulas ++= inf.assumedFormulas
          selectedInferences = inf :: selectedInferences
        }
    
      if (selectedInferences.isEmpty)
        child
      else
        BranchInferenceCertificate(selectedInferences, child, order)
    }
  
  override def toString : String = inferences.toString
  
}

////////////////////////////////////////////////////////////////////////////////

trait BranchInferenceCollector extends ComputationLogger {
  def getCollection : BranchInferenceCollection
  
  /**
   * Inform the collector that a new formula has occurred on the branch
   * (important for alpha-rules)
   */
  def newFormula(f : Conjunction) : Unit

  /**
   * Inference corresponding to an application of the <code>col-red</code> or
   * <code>col-red-subst</code> rule. This will simply introduce a new constant
   * <code>newSymbol</code> that is defined as the term
   * <code>newSymbolDef</code>.
   * 
   * This method is not added in the <code>ComputationLogger</code>, because it
   * is never used in the ter/for datastructures.
   */
  def columnReduce(oldSymbol : ConstantTerm, newSymbol : ConstantTerm,
                   newSymbolDef : LinearCombination, subst : Boolean,
                   newOrder : TermOrder) : Unit
  
  /**
   * Inference corresponding to applications of the rules <code>all-left</code>,
   * <code>ex-left</code>, etc. A uniform prefix of quantifiers (only forall or
   * only exists) is instantiated with a single inference.
   * <code>newConstants</code> are the constants introduced to instantiate the
   * quantifiers, starting with the innermost instantiated quantifier.
   */
  def instantiateQuantifier(quantifiedFormula : Conjunction,
                            newConstants : Seq[ConstantTerm],
                            result : Conjunction,
                            order : TermOrder) : Unit

  /**
   * An inference that turns a universally quantified divisibility constraint into
   * an existentially quantified disjunction equations.
   */
  def divRight(divisibility : Conjunction,
               result : Conjunction, order : TermOrder) : Unit
}

object NonLoggingBranchInferenceCollector
       extends ComputationLogger.NonLoggingLogger with BranchInferenceCollector {
  def newFormula(f : Conjunction) : Unit = {}
  def getCollection : BranchInferenceCollection = BranchInferenceCollection.EMPTY
  def columnReduce(oldSymbol : ConstantTerm, newSymbol : ConstantTerm,
                   newSymbolDef : LinearCombination, subst : Boolean,
                   newOrder : TermOrder) : Unit = {}
  def instantiateQuantifier(quantifiedFormula : Conjunction,
                            newConstants : Seq[ConstantTerm],
                            result : Conjunction,
                            order : TermOrder) : Unit = {}
  def divRight(divisibility : Conjunction,
               result : Conjunction, order : TermOrder) : Unit = {}
}

////////////////////////////////////////////////////////////////////////////////

object LoggingBranchInferenceCollector {
  def empty = new LoggingBranchInferenceCollector(List())
  def apply(inferences : List[BranchInference]) =
    new LoggingBranchInferenceCollector(inferences)
}

/**
 * Mutable datastructure for collecting inferences during some computation. To
 * avoid having to pass around collectors all over the place, a dynamic variable
 * is used to realise context collectors.
 */
class LoggingBranchInferenceCollector private
      (var inferences : List[BranchInference])
      extends {

  val isLogging = true

} with BranchInferenceCollector {
  
  def apply(inf : BranchInference) : Unit = {
    inferences = inf :: inferences
    for (f <- inf.providedFormulas) newFormula(f)
  }

  def newFormula(f : Conjunction) : Unit =
    for (alphaInf <- BranchInferenceCollection genAlphaInferences f)
      inferences = alphaInf :: inferences
  
  def getCollection : BranchInferenceCollection =
    BranchInferenceCollection(inferences)
  
  //////////////////////////////////////////////////////////////////////////////
  
  def combineEquations(equations : Seq[(IdealInt, LinearCombination)],
                       result : LinearCombination,
                       order : TermOrder) : Unit = {
    implicit val o = order
    apply(CombineEquationsInference(for ((c, lc) <- equations) yield (c, lc === 0),
                                    result === 0,
                                    order))
  }

  def reduceArithFormula(equations : Seq[(IdealInt, LinearCombination)],
                         targetLit : ArithConj, result : ArithConj,
                         order : TermOrder) : Unit = {
    implicit val o = order
    apply(ReduceInference(for ((c, lc) <- equations) yield (c, lc === 0),
                          targetLit, result,
                          order))
  }

  def reducePredFormula(equations : Seq[Seq[(IdealInt, LinearCombination)]],
                        targetLit : PredConj, result : PredConj,
                        order : TermOrder) : Unit = {
    implicit val o = order
    apply(ReducePredInference(for (eqs <- equations) yield
                                (for ((c, lc) <- eqs) yield (c, lc === 0)),
                              targetLit, result,
                              order))
  }

  def combineInequalities(leftCoeff : IdealInt, leftInEq : LinearCombination,
                          rightCoeff : IdealInt, rightInEq : LinearCombination,
                          result : LinearCombination,
                          order : TermOrder) : Unit = {
    implicit val o = order
    apply(CombineInequalitiesInference(leftCoeff, leftInEq >= 0,
                                       rightCoeff, rightInEq >= 0,
                                       result >= 0, order))
  }

  def antiSymmetry(leftInEq : LinearCombination, rightInEq : LinearCombination,
                   order : TermOrder) : Unit = {
    implicit val o = order
    apply(AntiSymmetryInference(leftInEq >= 0, rightInEq >= 0,
                                leftInEq === 0, order))
  }

  def directStrengthen(inequality : LinearCombination, equation : LinearCombination,
                       result : LinearCombination, order : TermOrder) : Unit = {
    implicit val o = order
    apply(DirectStrengthenInference(inequality >= 0, equation =/= 0,
                                    result >= 0, order))
  }
  
  def columnReduce(oldSymbol : ConstantTerm, newSymbol : ConstantTerm,
                   newSymbolDef : LinearCombination, subst : Boolean,
                   newOrder : TermOrder) : Unit = {
    implicit val o = newOrder
    apply(ColumnReduceInference(oldSymbol, newSymbol,
                                newSymbol === newSymbolDef, subst, newOrder))
  }

  def instantiateQuantifier(quantifiedFormula : Conjunction,
                            newConstants : Seq[ConstantTerm],
                            result : Conjunction,
                            order : TermOrder) : Unit =
    apply(QuantifierInference(quantifiedFormula, newConstants, result, order))

  def groundInstantiateQuantifier(quantifiedFormula : Conjunction,
                                  instanceTerms : Seq[LinearCombination],
                                  result : Conjunction,
                                  order : TermOrder) : Unit =
    apply(GroundInstInference(quantifiedFormula, instanceTerms, result, order))

  def divRight(divisibility : Conjunction,
               result : Conjunction, order : TermOrder) : Unit =
    apply(DivRightInference(divisibility, result, order))

  def unifyPredicates(leftAtom : Atom, rightAtom : Atom,
                      result : EquationConj, order : TermOrder) : Unit =
    apply(PredUnifyInference(leftAtom, rightAtom, result, order))

}
