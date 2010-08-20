/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, ConstantTerm, Formula}
import ap.terfor.preds.{PredConj, Predicate}
import ap.parser.{PartName, IInterpolantSpec}
import ap.terfor.TerForConvenience._
import ap.util.Debug

object InterpolationContext {
  
  private val AC = Debug.AC_INTERPOLATION
  
  def apply(namedParts : Map[PartName, Conjunction],
            spec : IInterpolantSpec,
            order : TermOrder) =
    new InterpolationContext (
      Set()++(for(name<- spec.left.iterator) yield namedParts(name).negate),
      Set()++(for(name<- spec.right.iterator) yield namedParts(name).negate),
      Set()++(for (f <- (namedParts get PartName.NO_NAME).iterator) yield f.negate),
      Map(), Map(), Set(), order)
  
  def apply(leftFormulas : Iterable[Conjunction],
            rightFormulas : Iterable[Conjunction],
            commonFormulas : Iterable[Conjunction],
            order : TermOrder) =
    new InterpolationContext (Set() ++ (for (f <- leftFormulas.iterator) yield f.negate),
                              Set() ++ (for (f <- rightFormulas.iterator) yield f.negate),
                              Set() ++ (for (f <- commonFormulas.iterator) yield f.negate),
                              Map(), Map(), Set(), order)
  
}

class InterpolationContext(
  val leftFormulae : Set[Conjunction],
  val rightFormulae : Set[Conjunction],
  val commonFormulae : Set[Conjunction],
  partialInterpolants : Map[ArithConj, PartialInterpolant],
  rewrittenPredAtoms : Map[PredConj, (Seq[Seq[(IdealInt, EquationConj)]], PredConj)],
  val parameters : Set[ConstantTerm],
  val order : TermOrder)
{
   private def getConstants(fors : Iterable[Formula]) =
     Set() ++ (for(f <- fors.iterator; c <- f.constants.iterator) yield c)

   private def getPredicates(fors : Iterable[Formula]) =
     Set() ++ (for(f <- fors.iterator; p <- f.predicates.iterator) yield p)
   
   lazy val commonFormulaConstants = getConstants(commonFormulae)
  
   lazy val leftConstants = getConstants(leftFormulae)
   lazy val rightConstants = getConstants(rightFormulae)
   lazy val allConstants =
     leftConstants ++ rightConstants ++ commonFormulaConstants
   
   lazy val leftLocalConstants =  leftConstants -- rightConstants
   lazy val rightLocalConstants =  rightConstants -- leftConstants
   
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
  
  
  def addPartialInterpolant(literal : ArithConj,
                            partialInter : PartialInterpolant) : InterpolationContext =
  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC, partialInter compatible literal)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val newPartialInterpolants = partialInterpolants + (literal -> partialInter)
    
    new InterpolationContext(
      leftFormulae, rightFormulae, commonFormulae, newPartialInterpolants,
      rewrittenPredAtoms, parameters, order)
  }
  
  def getPartialInterpolant(literal : ArithConj) : PartialInterpolant =
  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC, literal.isLiteral)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    (partialInterpolants get literal) match {
      case Some(res) => res
      case None => {
        val ArithConj(posEqs, negEqs, inEqs) = literal
        
        if (isFromLeft(literal)) {
          if (!posEqs.isTrue)
            PartialInterpolant eqLeft posEqs(0)
          else if (!negEqs.isTrue)
            PartialInterpolant eqRight negEqs(0)
          else
            PartialInterpolant inEqLeft inEqs(0)
        } else if (isFromRight(literal)) {
          if (!posEqs.isTrue)
            PartialInterpolant eqLeft 0
          else if (!negEqs.isTrue)
            PartialInterpolant negEqRight 0
          else
            PartialInterpolant inEqLeft 0
        } else
          throw new Error("The arithmetic atom " + literal + " was not found")
      }
    }
  }
  
  def getPredAtomRewriting(rewrittenLit : PredConj)
                          : (Seq[Seq[(IdealInt, EquationConj)]], PredConj) = {
    val pred = rewrittenLit.predicates.iterator.next
    rewrittenPredAtoms.getOrElse(rewrittenLit,
                                 (Array.fill(pred.arity)(List()), rewrittenLit))
  }
  
  def isRewrittenLeftLit(lit : PredConj) : Boolean = {
    val (_, oriLit) = getPredAtomRewriting(lit)
    isFromLeft(oriLit)
  }
  
  def isRewrittenRightLit(lit : PredConj) : Boolean = {
    val (_, oriLit) = getPredAtomRewriting(lit)
    isFromRight(oriLit)
  }
  
  def rewritePredAtom(equations : Seq[Seq[(IdealInt, EquationConj)]],
                      targetLit : PredConj,
                      result : PredConj) : InterpolationContext = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC,
                    targetLit.isLiteral && result.isLiteral &&
                    targetLit.positiveLits.isEmpty == result.positiveLits.isEmpty &&
                    targetLit.predicates == result.predicates)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (oldEqs, oriLit) = getPredAtomRewriting(targetLit)
    val newEqs = (for ((eqs1, eqs2) <- oldEqs.iterator zip equations.iterator)
                    yield (eqs1 ++ eqs2)).toList
    
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms + (result -> (newEqs, oriLit)),
                             parameters, order)
  }
 
  def isFromLeft(conj : Conjunction) : Boolean = leftFormulae contains conj
 
  def isFromRight(conj : Conjunction) : Boolean = rightFormulae contains conj

  def isCommon(conj : Conjunction) : Boolean = commonFormulae contains conj

  def addConstant(const : ConstantTerm) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             if(order.orderedConstants contains const) order
                             else order.extend(const, Set()))
  
  def addConstants(consts : Seq[ConstantTerm]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             (order /: consts)(_.extend(_, Set())))

  def addParameter(const : ConstantTerm) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters + const,
                             if(order.orderedConstants contains const) order
                             else order.extend(const, Set()))
  
  def addLeft(left : Conjunction) : InterpolationContext =
    new InterpolationContext(leftFormulae + left, rightFormulae,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addLeft(lefts : Iterable[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae ++ lefts, rightFormulae,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addLeft(lefts : Iterator[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae ++ lefts, rightFormulae,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)

  def addRight(right : Conjunction) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae + right,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms, 
                             parameters,
                             order)
  
  def addRight(rights : Iterable[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae ++ rights,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms, 
                             parameters,
                             order)
  
  def addRight(rights : Iterator[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae ++ rights,
                             commonFormulae,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addCommon(common : Conjunction) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae + common,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addCommon(commons : Iterable[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae ++ commons,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def addCommon(commons : Iterator[Conjunction]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae ++ commons,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             order)
  
  def setOrder(newOrder : TermOrder) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             partialInterpolants, rewrittenPredAtoms,
                             parameters, newOrder)
}

