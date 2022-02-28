/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap.basetypes.IdealInt
import ap.parser.{PartName, IInterpolantSpec}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.{TermOrder, ConstantTerm, Formula}
import ap.terfor.preds.Predicate
import ap.terfor.substitutions.{IdentitySubst, ConstantSubst}
import ap.terfor.TerForConvenience._
import ap.proof.certificates.{CertFormula, CertArithLiteral, CertEquation,
                              CertNegEquation, CertInequality, CertPredLiteral}
import ap.util.{Debug, LazyMappedMap, Seqs}

object InterpolationContext {
  
  private val AC = Debug.AC_INTERPOLATION
  
  def apply(namedParts : Map[PartName, Conjunction],
            spec : IInterpolantSpec,
            order : TermOrder) : InterpolationContext =
    apply(for(name <- spec.left) yield namedParts(name),
          for(name <- spec.right) yield namedParts(name),
          for (n <- PartName.predefNames; f <- namedParts get n) yield f,
          order)
  
  def apply(leftFormulas : Iterable[Conjunction],
            rightFormulas : Iterable[Conjunction],
            commonFormulas : Iterable[Conjunction],
            order : TermOrder) : InterpolationContext = {
    val leftCertFors = toCertFormulaSet(leftFormulas)
    val rightCertFors = toCertFormulaSet(rightFormulas)
    new InterpolationContext (leftCertFors, rightCertFors,
                              toCertFormulaSet(commonFormulas),
                              getConstants(leftCertFors).toSet,
                              getConstants(rightCertFors).toSet,
                              Map(), Map(), Set(), Map(), order)
  }
 
  private def toCertFormulaSet(fors : Iterable[Conjunction]) =
    (for (f <- fors.iterator) yield CertFormula(f.negate)).toSet

  private def getConstants(fors : Iterable[CertFormula]) =
    for(f <- fors.iterator; c <- f.constants.iterator) yield c

  private def getPredicates(fors : Iterable[CertFormula]) =
    (for (f <- fors.iterator; p <- f.predicates.iterator) yield p).toSet
}

////////////////////////////////////////////////////////////////////////////////

class InterpolationContext private (val leftFormulae : Set[CertFormula],
                                    val rightFormulae : Set[CertFormula],
                                    val commonFormulae : Set[CertFormula],
                                    val leftConstants : Set[ConstantTerm],
                                    val rightConstants : Set[ConstantTerm],
                                    val partialInterpolants : Map[CertArithLiteral,
                                                                  PartialInterpolant],
                                    rewrittenPredAtoms : Map[CertPredLiteral,
                                                             (Seq[Seq[(IdealInt, CertEquation)]],
                                                              CertPredLiteral)],
                                    val parameters : Set[ConstantTerm],
                                    // constants that really represent a sum "c + d" of two
                                    // constants. those are are used to represent combined
                                    // application of col-red-l, col-red-r
                                    val doubleConstants : Map[ConstantTerm, (ConstantTerm, ConstantTerm)],
                                    val order : TermOrder) {

  import InterpolationContext._
  
  lazy val leftLocalConstants = leftConstants -- rightConstants
  lazy val rightLocalConstants = rightConstants -- leftConstants

  // not used very often
  lazy val commonFormulaConstants = getConstants(commonFormulae).toSet

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

  def addDoubleConstants(consts : Iterable[ConstantTerm])
                        : Iterator[ConstantTerm] =
    addDoubleConstants(consts.iterator)

  def addDoubleConstants(consts : Iterator[ConstantTerm])
                        : Iterator[ConstantTerm] =
    if (doubleConstants.isEmpty) {
      consts
    } else {
      for (c <- consts;
           d <- (doubleConstants get c) match {
                  case Some((d1, d2)) => Iterator(c, d1, d2)
                  case None           => Iterator single c
                })
      yield d
    }

  lazy val doubleConstantsSubst =
    if (doubleConstants.isEmpty) {
      new IdentitySubst (order)
    } else {
      val map = new LazyMappedMap[ConstantTerm, (ConstantTerm, ConstantTerm),
                                  ConstantTerm, LinearCombination](
                                  doubleConstants,
                                  (c:ConstantTerm) => c,
                                  { case c : ConstantTerm => c }, {
        case (c1, c2) =>
          LinearCombination(Array((IdealInt.ONE, c1), (IdealInt.ONE, c2)),
                            order)
      })
      ConstantSubst(map, order)
    }
  
  def addPartialInterpolant(
        literal : CertArithLiteral,
        partialInter : PartialInterpolant) : InterpolationContext = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InterpolationContext.AC,
                    (partialInter compatible literal) &&
                    Seqs.disjoint(partialInter.linComb.constants,
                                  doubleConstants.keySet))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val newPartialInterpolants = partialInterpolants + (literal -> partialInter)
    
    new InterpolationContext(
      leftFormulae, rightFormulae, commonFormulae,
      leftConstants, rightConstants, newPartialInterpolants,
      rewrittenPredAtoms, parameters, doubleConstants, order)
  }
  
  def getPartialInterpolant(literal : CertArithLiteral) : PartialInterpolant =
    (partialInterpolants get literal) match {
      case Some(res) => res
      case None =>
        if (isFromLeft(literal)) literal match {
          case CertEquation(lhs) =>
            PartialInterpolant eqLeft doubleConstantsSubst(lhs)
          case CertNegEquation(lhs) =>
            PartialInterpolant eqRight doubleConstantsSubst(lhs)
          case CertInequality(lhs) =>
            PartialInterpolant inEqLeft doubleConstantsSubst(lhs)
        } else if (isFromRight(literal)) literal match {
          case CertEquation(_) =>
            PartialInterpolant eqLeft LinearCombination.ZERO
          case CertNegEquation(_) =>
            PartialInterpolant negEqRight LinearCombination.ZERO
          case CertInequality(_) =>
            PartialInterpolant inEqLeft LinearCombination.ZERO
        } else {
          throw new Error("The arithmetic atom " + literal + " was not found")
        }
    }
  
  def getPIConverseFormula(literal : CertArithLiteral) : Formula = {
    val pi = getPartialInterpolant(literal)
    val lc = LinearCombination.sum(
               pi.den, doubleConstantsSubst(literal.lhs),
               IdealInt.MINUS_ONE, pi.linComb,
               order)

    import PartialInterpolant.Kind._
    pi.kind match {
      case EqLeft | EqRight => EquationConj(lc, order)
      case InEqLeft => InEqConj(lc, order)
      case NegEqRight => NegEquationConj(lc, order)
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
                             partialInterpolants,
                             rewrittenPredAtoms + (result -> (newEqs, oriLit)),
                             parameters, doubleConstants, order)
  }
 
  def isFromLeft(conj : CertFormula) : Boolean = leftFormulae contains conj
 
  def isFromRight(conj : CertFormula) : Boolean = rightFormulae contains conj

  def isCommon(conj : CertFormula) : Boolean = commonFormulae contains conj

  def addConstants(consts : Seq[ConstantTerm]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             leftConstants, rightConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order extend consts)

  def addParameter(const : ConstantTerm) : InterpolationContext =
    if (order.orderedConstants contains const)
      this
    else
      new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                               leftConstants, rightConstants,
                               partialInterpolants,
                               rewrittenPredAtoms,
                               parameters + const,
                               doubleConstants,
                               order.extend(const))
  
  def addDoubleConstant(const : ConstantTerm,
                        d1 : ConstantTerm,
                        d2 : ConstantTerm) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae,
                             leftConstants + d1,
                             rightConstants + d2,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters,
                             doubleConstants + (const -> (d1, d2)),
                             order)

  def addLeft(left : CertFormula) : InterpolationContext =
    new InterpolationContext(leftFormulae + left, rightFormulae,
                             commonFormulae,
                             leftConstants ++ addDoubleConstants(left.constants),
                             rightConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def addLeft(lefts : Iterable[CertFormula]) : InterpolationContext =
    new InterpolationContext(leftFormulae ++ lefts, rightFormulae,
                             commonFormulae,
                             leftConstants ++ addDoubleConstants(getConstants(lefts)),
                             rightConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def addRight(right : CertFormula) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae + right,
                             commonFormulae,
                             leftConstants,
                             rightConstants ++ addDoubleConstants(right.constants),
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def addRight(rights : Iterable[CertFormula]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae ++ rights,
                             commonFormulae,
                             leftConstants,
                             rightConstants ++ addDoubleConstants(getConstants(rights)),
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def addCommon(common : CertFormula) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae + common,
                             leftConstants,
                             rightConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def addCommon(commons : Iterable[CertFormula]) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae,
                             commonFormulae ++ commons,
                             leftConstants, rightConstants,
                             partialInterpolants,
                             rewrittenPredAtoms,
                             parameters, doubleConstants,
                             order)
  
  def setOrder(newOrder : TermOrder) : InterpolationContext =
    new InterpolationContext(leftFormulae, rightFormulae, commonFormulae,
                             leftConstants, rightConstants,
                             partialInterpolants, rewrittenPredAtoms,
                             parameters, doubleConstants, newOrder)
}

