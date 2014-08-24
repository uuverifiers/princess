/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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
import ap.util.{Seqs, Debug}

import scala.collection.mutable.{HashSet => MHashSet}

object BranchInferenceCollection {
  private val AC = Debug.AC_CERTIFICATES
  
  val EMPTY = new BranchInferenceCollection(List())

  def apply(initialFors : Iterable[Conjunction]) : BranchInferenceCollection =
    applyCert(for (c <- initialFors) yield CertFormula(c))
  
  def applyCert(initialFors : Iterable[CertFormula]) : BranchInferenceCollection =
    if (initialFors.isEmpty)
      EMPTY
    else
      apply((for (f <- initialFors;
                  inf <- genDefaultInferences(f)) yield inf).toList)
  
  def apply(inferences : List[BranchInference]) =
    new BranchInferenceCollection(inferences)
  
  /**
   * Check whether alpha or simplification rules are applicable to the given
   * formula
   */
  private[certificates]
    def genDefaultInferences(f : CertFormula) : Seq[BranchInference] = {
      val alphaInfs = genAlphaInferences(f)
      val directSimpInfs = genSimpInferences(f)
      val indirectSimpInfs = for (inf <- alphaInfs;
                                  f <- inf.providedFormulas;
                                  i <- genSimpInferences(f)) yield i
      alphaInfs ++ directSimpInfs ++ indirectSimpInfs
    }
  
  /**
   * Generate applications of the alpha rule to the given conjunction
   */
  private def genAlphaInferences(cf : CertFormula) : Seq[BranchInference] =
    cf match {
      case cf@CertCompoundFormula(f) if (f.size > 1 && f.quans.isEmpty) =>
        List(AlphaInference(cf, Set() ++ (for (l <- f.iterator) yield CertFormula(l))))
      case _ => List()
    }

  /**
   * Check whether the given formula can be simplified, and generate a
   * corresponding inference in this case
   */
  private def genSimpInferences(f : CertFormula) : Seq[BranchInference] =
    if (f.isTrue || f.isFalse) {
      List()
    } else f match {
      case f@CertInequality(lhs) => {
        val simplified = lhs.makePrimitive
        if (simplified == lhs)
          List()
        else
          List(SimpInference(f, CertInequality(simplified), f.order))
      }
      case f : CertArithLiteral => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, f.isInstanceOf[CertEquation] ||
                            f.isInstanceOf[CertNegEquation])
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val simplified = f.lhs.makePrimitiveAndPositive
        if (simplified == f.lhs)
          List()
        else
          List(SimpInference(f, f update simplified, f.order))
      }
      case _ => List()
    }
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
      val requiredFormulas = new MHashSet[CertFormula]
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
  
  /**
   * Check whether any of the stored inferences produced an unsatisfiable
   * formula
   */
  def findFalseFormula : Option[CertFormula] =
    (for (inf <- inferences.iterator;
          f <- inf.providedFormulas.iterator) yield f) find (_.isFalse)
  
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
   * an existentially quantified disjunction of equations.
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
  private val AC = Debug.AC_CERTIFICATES

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
  
  private def addPlusDefaultInfs(inf : BranchInference) : Unit = {
    addDirectly(inf)
    for (f <- inf.providedFormulas) newCertFormula(f)
  }

  private def addDirectly(inf : BranchInference) : Unit =
    inferences = inf :: inferences
  
  def newFormula(f : Conjunction) : Unit = newCertFormula(CertFormula(f))
  
  private def newCertFormula(f : CertFormula) : Unit =
    for (alphaInf <- BranchInferenceCollection genDefaultInferences f)
      addDirectly(alphaInf)
  
  def getCollection : BranchInferenceCollection =
    BranchInferenceCollection(inferences)
  
  //////////////////////////////////////////////////////////////////////////////
  
  def combineEquations(equations : Seq[(IdealInt, LinearCombination)],
                       result : LinearCombination,
                       resultAfterRounding : LinearCombination,
                       order : TermOrder) : Unit = {
    val resultF = CertEquation(result)
    addDirectly(CombineEquationsInference(for ((c, lc) <- equations) yield (c, CertEquation(lc)),
                                          resultF, order))
    if (result != resultAfterRounding)
      addDirectly(SimpInference(resultF, CertEquation(resultAfterRounding), order))
  }

  def reduceNegEquation(equations : Seq[(IdealInt, LinearCombination)],
                        targetLit : LinearCombination, order : TermOrder) : Unit =
    addPlusDefaultInfs(ReduceInference(for ((c, lc) <- equations) yield (c, CertEquation(lc)),
                                       CertNegEquation(targetLit), order))

  def reduceInequality(equations : Seq[(IdealInt, LinearCombination)],
                       targetLit : LinearCombination, order : TermOrder) : Unit =
    addPlusDefaultInfs(ReduceInference(for ((c, lc) <- equations) yield (c, CertEquation(lc)),
                                       CertInequality(targetLit), order))

  def reducePredFormula(equations : Seq[Seq[(IdealInt, LinearCombination)]],
                        targetLit : Atom, negated : Boolean, result : Atom,
                        order : TermOrder) : Unit =
    addPlusDefaultInfs(ReducePredInference(for (eqs <- equations) yield
                                             (for ((c, lc) <- eqs) yield (c, CertEquation(lc))),
                                           CertPredLiteral(negated, targetLit),
                                           CertPredLiteral(negated, result),
                                           order))

  def combineInequalities(leftCoeff : IdealInt, leftInEq : LinearCombination,
                          rightCoeff : IdealInt, rightInEq : LinearCombination,
                          result : LinearCombination,
                          resultAfterRounding : LinearCombination,
                          order : TermOrder) : Unit = {
    val resultF = CertInequality(result)
    addDirectly(CombineInequalitiesInference(leftCoeff, CertInequality(leftInEq),
                                             rightCoeff, CertInequality(rightInEq),
                                             resultF, order))
    if (result != resultAfterRounding)
      addDirectly(SimpInference(resultF, CertInequality(resultAfterRounding), order))
  }

  def antiSymmetry(leftInEq : LinearCombination, rightInEq : LinearCombination,
                   order : TermOrder) : Unit =
    addDirectly(AntiSymmetryInference(CertInequality(leftInEq),
                                      CertInequality(rightInEq),
                                      order))

  def directStrengthen(inequality : LinearCombination, equation : LinearCombination,
                       result : LinearCombination, order : TermOrder) : Unit =
    addDirectly(DirectStrengthenInference(CertInequality(inequality),
                                          CertNegEquation(equation),
                                          CertInequality(result),
                                          order))
  
  def columnReduce(oldSymbol : ConstantTerm, newSymbol : ConstantTerm,
                   newSymbolDef : LinearCombination, subst : Boolean,
                   newOrder : TermOrder) : Unit = {
    implicit val o = newOrder
    addDirectly(ColumnReduceInference(oldSymbol, newSymbol,
                                      CertEquation(newSymbolDef - newSymbol),
                                      subst, newOrder))
  }

  def instantiateQuantifier(quantifiedFormula : Conjunction,
                            newConstants : Seq[ConstantTerm],
                            result : Conjunction,
                            order : TermOrder) : Unit =
    addPlusDefaultInfs(QuantifierInference(CertCompoundFormula(quantifiedFormula),
                                           newConstants,
                                           CertFormula(result),
                                           order))

  def groundInstantiateQuantifier(quantifiedFormula : Conjunction,
                                  instanceTerms : Seq[LinearCombination],
                                  result : Conjunction,
                                  order : TermOrder) : Unit =
    addPlusDefaultInfs(GroundInstInference(CertCompoundFormula(quantifiedFormula),
                                           instanceTerms,
                                           CertFormula(result),
                                           order))

  def divRight(divisibility : Conjunction,
               result : Conjunction, order : TermOrder) : Unit =
    addDirectly(DivRightInference(CertCompoundFormula(divisibility),
                                  CertCompoundFormula(result),
                                  order))

  def unifyPredicates(leftAtom : Atom, rightAtom : Atom,
                      result : EquationConj, order : TermOrder) : Unit =
    addPlusDefaultInfs(PredUnifyInference(leftAtom, rightAtom,
                                          CertFormula(result),
                                          order))

}
