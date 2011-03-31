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
  
  //////////////////////////////////////////////////////////////////////////////

  private def simplify(cert : Certificate)
        : (Certificate, WeakeningRange) = cert match {
    case cert@BetaCertificate(leftForm, rightForm, leftChild, rightChild, _) => {
      val (newLeft,  wLeft)  = simplify(leftChild)
      val (newRight, wRight) = simplify(rightChild)
      (cert.copy(_leftChild = newLeft, _rightChild = newRight),
       mergeWeakening(wLeft, wRight))
    }
    
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
              case (_, _, None) => wkn
              case _ => defaultWeakening
            }
            
          (inf :: newOtherInfs, newChild, newWeakening2)
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
 
  private def ineqSubset(s : Set[CertFormula]) = s collect {
    case f : CertInequality => f
  } 
}