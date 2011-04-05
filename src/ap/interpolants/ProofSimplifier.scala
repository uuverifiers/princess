/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.certificates._
import ap.util.Debug

/**
 * Module for simplifying a proof (certificate) by eliminating as many
 * rounding steps as possible; this is currently done in a rather naive way
 */
object ProofSimplifier {

  private val AC = Debug.AC_INTERPOLATION

  type WeakeningRange = Map[CertInequality, IdealInt]
  
  def apply(cert : Certificate) : Certificate = simplify(cert) _1
  
  //////////////////////////////////////////////////////////////////////////////

  private def simplify(cert : Certificate)
        : (Certificate, WeakeningRange) = cert match {
    
    case CloseCertificate(contradFors, _) => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////       
      Debug.assertInt(AC, contradFors.size == 1 && contradFors.head.isFalse)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      contradFors.head match {
        case f@CertInequality(lc) => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////       
          Debug.assertInt(AC, lc.isConstant && lc.constant.signum < 0)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          (cert, Map(f -> (-lc.constant - 1)))
        }
        case _ =>
          (cert, Map())
      }
    }
    
    case cert@BranchInferenceCertificate(infs, child, _) => {
      val (newInfs, newChild, wr) = simplifyInfs(infs.toList, child)
      if (newInfs.isEmpty)
        (newChild, wr)
      else
        (cert.copy(inferences = newInfs, _child = newChild), wr)
    }
    
    case cert => {
      val (newChildren, weakenings) =
        (for (c <- cert.subCertificates) yield simplify(c)).unzip
      (cert update newChildren, weakenings reduceLeft mergeWeakening)
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def simplifyInfs(infs : List[BranchInference], child : Certificate)
        : (List[BranchInference], Certificate, WeakeningRange) = infs match {

    case List() => {
      val (newChild, weakening) = simplify(child)
      (List(), newChild, weakening)
    }
    
    case inf :: otherInfs => {
      val (newOtherInfs, newChild, wkn) = simplifyInfs(otherInfs, child)
      
      lazy val defaultWeakening =
        wkn -- ineqSubset(inf.providedFormulas) ++ (
          for (f <- ineqSubset(inf.assumedFormulas)) yield (f -> IdealInt.ZERO))
      
      inf match {
        case inf@ReduceInference(_, target : CertInequality,
                                 result : CertInequality, _) => {
          val newWeakening2 =
            (wkn get target, wkn get result) match {
              case (None, Some(resultW)) => wkn - result + (target -> resultW)
              case (_, None)             => wkn
              case _                     => defaultWeakening
            }
          
          (inf :: newOtherInfs, newChild, newWeakening2)
        }
        
        case inf@CombineInequalitiesInference(leftCoeff, leftInEq,
                                              rightCoeff, rightInEq, result, _) => {
          val newWeakening2 =
            (wkn get leftInEq, wkn get rightInEq, wkn get result) match {
              case (None, None, Some(resultW)) =>
                wkn - result + (leftInEq -> (resultW / leftCoeff),
                                rightInEq -> (resultW / rightCoeff))
              case (_, _, None)                => wkn
              case _                           => defaultWeakening
            }
            
          (inf :: newOtherInfs, newChild, newWeakening2)
        }
                  
        case inf@SimpInference(target : CertInequality,
                               result : CertInequality, _) =>
          if (inf.constantDiff.isZero) {
            // nothing to be simplified, but we can propagate the weakening
            // bound
            val newWeakening2 =
              (wkn get target, wkn get result) match {
                case (None, Some(resultW)) => wkn - result + (target -> resultW)
                case (_, None)             => wkn
                case _                     => defaultWeakening
              }
            (inf :: newOtherInfs, newChild, newWeakening2)
          } else (wkn get result) match {
            case Some(resultW) if (inf.constantDiff <= resultW * inf.factor) => {
              // The simplification can be eliminated: everywhere in this
              // subproof, replace <code>result</code> with
              // <code>target = result * factor + constantDiff</code>
              val (newOtherInfs2, newChild2) =
                elimSimpInfs(newOtherInfs, newChild,
                             Map(result -> (target, inf.factor, inf.constantDiff)))
         
              simplifyInfs(newOtherInfs2, newChild2)
            }
            case _ => {
              // it might be possible to eliminate simplifications before this
              // one
              val newTargetW =
                wkn.getOrElse(target, inf.factor) min (inf.factor - inf.constantDiff - 1)
              val newWeakening2 =
                wkn - result + (target -> newTargetW)
              (inf :: newOtherInfs, newChild, newWeakening2)
            }
          }
                                              
        case inf => (inf :: newOtherInfs, newChild, defaultWeakening)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def mergeWeakening(a : WeakeningRange, b : WeakeningRange)
                          : WeakeningRange =
    (a /: b) { case (newBounds, (ineq, bound)) =>
      newBounds + (ineq -> (bound min newBounds.getOrElse(ineq, bound)))
    }
 
  private def ineqSubset(s : Set[CertFormula]) =
    s collect { case f : CertInequality => f }

  //////////////////////////////////////////////////////////////////////////////

  type ReplMap = Map[CertInequality, (CertInequality, IdealInt, IdealInt)]
  
  private def elimSimp(cert : Certificate,
                       replacement : ReplMap) : Certificate = cert match {
    case cert@CloseCertificate(contradFors, _) => {
      val newContrad =
        for (f <- contradFors) yield f match {
          case f : CertInequality => replacement.getOrElse(f, (f, null, null)) _1
          case f => f
        }
      
      if (newContrad == contradFors)
        cert
      else
        cert.copy(localAssumedFormulas = newContrad)
    }

    case cert@BranchInferenceCertificate(infs, child, _) => {
      val (newInfs, newChild) = elimSimpInfs(infs.toList, child, replacement)
      if (newInfs.isEmpty)
        newChild
      else
        cert.copy(inferences = newInfs, _child = newChild)
    }

    case cert => {
      val newChildren =
        for ((c, i) <- cert.subCertificates.zipWithIndex)
          yield elimSimp(c, replacement -- ineqSubset(cert.localProvidedFormulas(i)))
      cert update newChildren
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimSimpInfs(infs : List[BranchInference], child : Certificate,
                           replacement : ReplMap)
                          : (List[BranchInference], Certificate) = infs match {

    case List() =>
      (List(), elimSimp(child, replacement))
    
    case inf :: otherInfs => {
      val (newInf, newRepl) = inf match {
        
        case inf@ReduceInference(equations,
                                 target : CertInequality,
                                 result : CertInequality, _)
          if (replacement contains target) => {
               
          val (newTarget, factor, constantDiff) = replacement(target)
          val newEquations = for ((c, eq) <- equations) yield (c * factor, eq)
          val newResult = CertInequality(result.lhs * factor + constantDiff)
          (List(inf.copy(equations = newEquations,
                         targetLit = newTarget, result = newResult)),
           replacement + (result -> (newResult, factor, constantDiff)))
        }
                  
        case inf@CombineInequalitiesInference(leftCoeff, leftInEq,
                                              rightCoeff, rightInEq, result, _)
          if ((replacement contains leftInEq) || (replacement contains rightInEq)) => {
              
          val (newLeft, leftFactor, leftDiff) =
            replacement.getOrElse(leftInEq, (leftInEq, IdealInt.ONE, IdealInt.ZERO))
          val (newRight, rightFactor, rightDiff) =
            replacement.getOrElse(rightInEq, (rightInEq, IdealInt.ONE, IdealInt.ZERO))

          val commonFactor = (leftFactor / (leftCoeff gcd leftFactor)) lcm
                             (rightFactor / (rightCoeff gcd rightFactor))
          val newLeftCoeff = commonFactor * leftCoeff / leftFactor
          val newRightCoeff = commonFactor * rightCoeff / rightFactor
          val commonDiff = newLeftCoeff * leftDiff + newRightCoeff * rightDiff
            
          val newResult = CertInequality(result.lhs * commonFactor + commonDiff)
            
          (List(inf.copy(leftCoeff = newLeftCoeff, leftInEq = newLeft,
                         rightCoeff = newRightCoeff, rightInEq = newRight,
                         result = newResult)),
           replacement + (result -> (newResult, commonFactor, commonDiff)))
        }

        case inf@SimpInference(target : CertInequality,
                               result : CertInequality, _)
          if (replacement contains target) => {

          val (newTarget, factor, constantDiff) = replacement(target)

          if (inf.constantDiff.isZero) {
            // just skip this simplification step
            (List(),
             replacement + (result -> (newTarget, factor * inf.factor, constantDiff)))
          } else {
            // the replacement should not change the result of the simplification
            (List(inf.copy(targetLit = newTarget)), replacement)
          }
        }
          
        case inf => (List(inf), replacement -- ineqSubset(inf.providedFormulas))
      }

      val (newOtherInfs, newChild) = elimSimpInfs(otherInfs, child, newRepl)
      (newInf ::: newOtherInfs, newChild)
    }
  }
}
