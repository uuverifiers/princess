/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap.basetypes.IdealInt
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, ConstantTerm, Formula}
import ap.terfor.preds.Predicate
import ap.parser.{PartName, IInterpolantSpec}
import ap.terfor.TerForConvenience._
import ap.proof.certificates.{CertFormula, CertArithLiteral, CertEquation,
                              CertNegEquation, CertInequality, CertPredLiteral}
import ap.util.Debug

object InterpolationContext {
  
  private val AC = Debug.AC_INTERPOLATION
  
  def apply(namedParts : Map[PartName, Conjunction],
            spec : IInterpolantSpec,
            order : TermOrder) : InterpolationContext =
    apply(for(name <- spec.left) yield namedParts(name),
          for(name <- spec.right) yield namedParts(name),
          namedParts get PartName.NO_NAME,
          order)
  
  def apply(leftFormulas : Iterable[Conjunction],
            rightFormulas : Iterable[Conjunction],
            commonFormulas : Iterable[Conjunction],
            order : TermOrder) : InterpolationContext = {
    val leftCertFors = toCertFormulaSet(leftFormulas)
    val rightCertFors = toCertFormulaSet(rightFormulas)
    val leftConstants = getConstants(leftCertFors)
    val rightConstants = getConstants(rightCertFors)
    new InterpolationContext (leftCertFors, rightCertFors,
                              toCertFormulaSet(commonFormulas),
                              leftConstants, rightConstants,
                              leftConstants -- rightConstants,
                              rightConstants -- leftConstants,
                              Map(), Map(), Set(), order)
  }
 
  private def toCertFormulaSet(fors : Iterable[Conjunction]) =
    Set() ++ (for (f <- fors.iterator) yield CertFormula(f.negate))

  private def getConstants(fors : Iterable[CertFormula]) =
    Set() ++ (for(f <- fors.iterator; c <- f.constants.iterator) yield c)

  private def getPredicates(fors : Iterable[CertFormula]) =
    Set() ++ (for(f <- fors.iterator; p <- f.predicates.iterator) yield p)
}

////////////////////////////////////////////////////////////////////////////////

class InterpolationContext private (val leftFormulae : Set[CertFormula],
                                    val rightFormulae : Set[CertFormula],
                                    val commonFormulae : Set[CertFormula],
                                    val leftConstants : Set[ConstantTerm],
                                    val rightConstants : Set[ConstantTerm],
                                    val leftLocalConstants : Set[ConstantTerm],
                                    val rightLocalConstants : Set[ConstantTerm],
                                    partialInterpolants : Map[CertArithLiteral, PartialInterpolant],
                                    rewrittenPredAtoms : Map[CertPredLiteral,
                                                             (Seq[Seq[(IdealInt, CertEquation)]],
                                                              CertPredLiteral)],
                                    val parameters : Set[ConstantTerm],
                                    val order : TermOrder) {

  import InterpolationContext._
  
  // not used very often
  lazy val commonFormulaConstants = getConstants(commonFormulae)

  lazy val allConstants =
    leftConstants ++ rightConstants ++ commonFormulaConstants

  lazy val globalConstants =
    (leftConstants & rightConstants) ++ commonFormulaConstants
  
  lazy val commonFormulaPredicates = getPredicates(commonFormulae)
  lazy val leftPredicates = getPredicates(leftFormulae)
  lazy val rightPredicates = getPredicates(rightFormulae)
   
  lazy val allPredicates =
    leftPredicates ++ rightPredicates ++ commonFormulaPredicates

  lazy val leftLocalPredicates = leftPredicates -- rightPredicates
  lazy val globalPredicates =
    (leftPredicates & rightPredicates) ++ commonFormulaPredicates
  
  def addPartialInterpolant(literal : CertArithLiteral,
                            partialInter : PartialInterpolant) : InterpolationContext = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC, partialInter compatible literal)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val newPartialInterpolants = partialInterpolants + (literal -> partialInter)
    
    new InterpolationContext(
      leftFormulae, rightFormulae, commonFormulae,
      leftConstants, rightConstants, leftLocalConstants, rightLocalConstants,
      newPartialInterpolants,
      rewrittenPredAtoms, parameters, order)
  }
  
  def getPartialInterpolant(literal : CertArithLiteral) : PartialInterpolant =
    (partialInterpolants get literal) match {
      case Some(res) => res
      case None =>
        if (isFromLeft(literal)) literal match {
          case CertEquation(lhs) => PartialInterpolant eqLeft lhs
          case CertNegEquation(lhs) => PartialInterpolant eqRight lhs
          case CertInequality(lhs) => PartialInterpolant inEqLeft lhs
        } else if (isFromRight(literal)) literal match {
          case CertEquation(_) => PartialInterpolant eqLeft LinearCombination.ZERO
          case CertNegEquation(_) => PartialInterpolant negEqRight LinearCombination.ZERO
          case CertInequality(_) => PartialInterpolant inEqLeft LinearCombination.ZERO
        } else {
          throw new Error("The arithmetic atom " + literal + " was not found")
        }
    }
  
  def getPredAtomRewriting(rewrittenLit : CertPredLiteral)
                          : (Seq[Seq[(IdealInt, CertEquation)]], CertPredLiteral) = {
    val pred = rewrittenLit.predicates.head
    rewrittenPredAtoms.getOrElse(rewrittenLit,
                                 (Array.fill(pred.arity)(List()), rewrittenLit))
  }
  
  def isRewrittenLeftLit(lit : CertPredLiteral) : Boolean = {
    val (_, oriLit) = getPredAtomRewriting(lit)
    isFromLeft(oriLit)
  }
  
  def isRewrittenRightLit(lit : CertPredLiteral) : Boolean = {
    val (_, oriLit) = getPredAtomRewriting(lit)
    isFromRight(oriLit)
  }
  
  def rewritePredAtom(equations : Seq[Seq[(IdealInt, CertEquation)]],
                      targetLit : CertPredLiteral,
                      result : CertPredLiteral) : InterpolationContext = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC,
                    targetLit.predicates == result.predicates)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (oldEqs, oriLit) = getPredAtomRewriting(targetLit)
    val newEqs = (for ((eqs1, eqs2) <- oldEqs.iterator zip equations.iterator)
                    yield (eqs1 ++ eqs2)).toList
    
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             leftConstants, rightConstants,
                             leftLocalConstants, rightLocalConstants,
                             partialInterpolants,
                             rewrittenPredAtoms + (result -> (newEqs, oriLit)),
                             parameters, order)
  }
 
  def isFromLeft(conj : CertFormula) : Boolean = leftFormulae contains conj
 
  def isFromRight(conj : CertFormula) : Boolean = rightFormulae contains conj

  def isCommon(conj : CertFormula) : Boolean = commonFormulae contains conj

  def addConstants(consts : Seq[ConstantTerm]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             leftConstants, rightConstants,
                             leftLocalConstants, rightLocalConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order extend consts)

  def addParameter(const : ConstantTerm) : InterpolationContext =
    if (order.orderedConstants contains const)
      this
    else
      new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                               leftConstants, rightConstants,
                               leftLocalConstants, rightLocalConstants,
                               partialInterpolants,
                               rewrittenPredAtoms,
                               parameters + const,
                               order.extend(const, Set()))
  
  def addLeft(left : CertFormula) : InterpolationContext =
    new InterpolationContext(leftFormulae + left, rightFormulae,
                             commonFormulae,
                             leftConstants ++ left.constants, rightConstants,
                             leftLocalConstants ++ (left.constants -- rightConstants),
                             rightLocalConstants -- left.constants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addLeft(lefts : Iterable[CertFormula]) : InterpolationContext = {
    val newConstants = getConstants(lefts)
    new InterpolationContext(leftFormulae ++ lefts, rightFormulae,
                             commonFormulae,
                             leftConstants ++ newConstants, rightConstants,
                             leftLocalConstants ++ (newConstants -- rightConstants),
                             rightLocalConstants -- newConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  }
  
  def addRight(right : CertFormula) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae + right,
                             commonFormulae,
                             leftConstants, rightConstants ++ right.constants,
                             leftLocalConstants -- right.constants,
                             rightLocalConstants ++ (right.constants -- leftConstants),
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addRight(rights : Iterable[CertFormula]) : InterpolationContext = {
    val newConstants = getConstants(rights)
    new InterpolationContext(leftFormulae, rightFormulae ++ rights,
                             commonFormulae,
                             leftConstants, rightConstants ++ getConstants(rights),
                             leftLocalConstants -- newConstants,
                             rightLocalConstants ++ (newConstants -- leftConstants),
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  }
  
  def addCommon(commons : Iterable[CertFormula]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae ++ commons,
                             leftConstants, rightConstants,
                             leftLocalConstants, rightLocalConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def setOrder(newOrder : TermOrder) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             leftConstants, rightConstants,
                             leftLocalConstants, rightLocalConstants,
                             partialInterpolants, rewrittenPredAtoms,
                             parameters, newOrder)
}

