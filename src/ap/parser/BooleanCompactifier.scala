/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs, PlainRange}

import IBinJunctor._
import IExpression._
import Quantifier._

/**
 * Transformation for pulling out common disjuncts/conjuncts from
 * conjunctions/disjunctions.
 */
object BooleanCompactifier {

  private val AC = Debug.AC_INPUT_ABSY
  
  def apply(f : IFormula) : IFormula = {
    val f1 = Transform2NNF(f)
    val f2 = CollectLiterals(f1)
    f2
  }

  //////////////////////////////////////////////////////////////////////////////

  private object CollectLiterals
                 extends CollectingVisitor[Unit, IExpression] {
    import SimpleClausifier.Literal
    import IBinJunctor._
    
    def apply(f : IFormula) : IFormula = this.visit(f, {}).asInstanceOf[IFormula]
    
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      t match {
        case t@ITimes(coeff, _) => subres(0) match {
          case IIntLit(value) => IIntLit(coeff * value)
          case ITimes(coeff2, s) => ITimes(coeff * coeff2, s)
          case _ => t update subres
        }
        
        case t@IPlus(_, _) => subres match {
          case Seq(IIntLit(value1), IIntLit(value2)) => IIntLit(value1 + value2)
          case _ => t update subres
        }
        
        case t@IIntFormula(IIntRelation.EqZero, _) => subres match {
          case Seq(IIntLit(value)) => IBoolLit(value.isZero)
          case _ => t update subres
        }
        
        case t@IIntFormula(IIntRelation.GeqZero, _) => subres match {
          case Seq(IIntLit(value)) => IBoolLit(value.signum >= 0)
          case _ => t update subres
        }
      
        case t@INot(_) => subres match {
          case Seq(IBoolLit(value)) => IBoolLit(!value)
          case _ => t update subres
        }
          
        case t@IBinFormula(j, _, _) => subres match {
          case Seq(s1@IBoolLit(false), s2) => j match {
            case And => s1
            case Or => s2
          }
          case Seq(s2, s1@IBoolLit(false)) => j match {
            case And => s1
            case Or => s2
          }
          case Seq(s1@IBoolLit(true), s2) => j match {
            case And => s2
            case Or => s1
          }
          case Seq(s2, s1@IBoolLit(true)) => j match {
            case And => s2
            case Or => s1
          }
          
          case Seq(IBinFormula(`j`, _, _), _) | Seq(_, IBinFormula(`j`, _, _)) =>
            // look at some larger formula containing this one
            t update subres
            
          case Seq(_ : IBinFormula, _) | Seq(_, _ : IBinFormula) => {
            val oppJ = j match {
              case And => Or
              case Or => And
            }
          
            val leftFors  = LineariseVisitor(subres(0).asInstanceOf[IFormula], oppJ)
            val rightFors = LineariseVisitor(subres(1).asInstanceOf[IFormula], oppJ)
            val rightForsSet = rightFors.toSet
          
            val commonFors = leftFors filter (rightForsSet contains _)

            if (commonFors.isEmpty) {
              t update subres
            } else {
              val commonForsSet = commonFors.toSet
            
              val newLeft =
                connect(leftFors.iterator filterNot (commonForsSet contains _), oppJ)
              val newRight =
                connect(rightFors.iterator filterNot (commonForsSet contains _), oppJ)
            
              IBinFormula(oppJ, connect(commonFors, oppJ),
                          IBinFormula(j, newLeft, newRight))
            }
          }
            
          case Seq(s1, s2) =>
            if (s1 == s2) s1 else (t update subres)
        }
      
        case t =>
          t update subres
      }
  }
  
  
}