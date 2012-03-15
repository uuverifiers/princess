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
                 extends CollectingVisitor[Unit, IFormula] {
    import SimpleClausifier.Literal
    import IBinJunctor._
    
    def apply(f : IFormula) : IFormula = this.visit(f, {})
    
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      t match {
        case Literal(t) =>
          // do not look into atoms
          ShortCutResult(t)
        case _ =>
          KeepArg
      }
  
    def postVisit(t : IExpression, arg : Unit, subres : Seq[IFormula]) : IFormula =
      t match {
        case t@IBinFormula(j, _, _)
          if (isBinFor(j, subres(0)) || isBinFor(j, subres(1))) =>
          // look at some larger formula containing this one
          t update subres

        case t@IBinFormula(j, _, _) => {
          val oppJ = j match {
            case And => Or
            case Or => And
          }
          
          val leftFors  = LineariseVisitor(subres(0), oppJ)
          val rightFors = LineariseVisitor(subres(1), oppJ)
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
        
        case t : IFormula =>
          t update subres
      }
    
    private def isBinFor(j : IBinJunctor.Value, f : IFormula) = f match {
      case IBinFormula(`j`, _, _) => true
      case _ => false
    }
  }
  
  
}