/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2020 Philipp Ruemmer <ph_r@gmx.net>
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
    
    def apply(f : IFormula) : IFormula =
      this.visit(f, {}).asInstanceOf[IFormula]
    
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      t match {
        case t@IBinFormula(j, _, _) => subres match {
          case Seq(IBinFormula(`j`, _, _), _) |
               Seq(_, IBinFormula(`j`, _, _)) =>
            // look at some larger formula containing this one
            t update subres
            
          case Seq(_ : IBinFormula, _) | Seq(_, _ : IBinFormula) => {
            val oppJ = j match {
              case And => Or
              case Or => And
            }
          
            val leftFors =
              LineariseVisitor(subres(0).asInstanceOf[IFormula], oppJ)
            val rightFors =
              LineariseVisitor(subres(1).asInstanceOf[IFormula], oppJ)
            val rightForsSet =
              rightFors.toSet

            val commonFors =
              leftFors filter (rightForsSet contains _)

            if (commonFors.isEmpty) {
              t update subres
            } else {
              val commonForsSet = commonFors.toSet
            
              val newLeft =
                connect(leftFors.iterator filterNot commonForsSet, oppJ)
              val newRight =
                connect(rightFors.iterator filterNot commonForsSet, oppJ)
            
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
