/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor;

import ap.util.{Debug, Logic, PlainRange, FilterIt}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.{ArithConj, ReduceWithAC}
import ap.terfor.preds.PredConj
import ap.terfor.conjunctions.{Conjunction, NegatedConjunctions, Quantifier}

/**
 * Some methods for generating random conjunctions
 */
class TestGenConjunctions {

   protected val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
   protected val vars = for (i <- Array.range(0, 20)) yield new VariableTerm(i)
   protected val constsVarsOne = consts ++ vars ++ List(OneTerm)
   val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
   val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c))
   
   protected def randomInput(len : Int) = for (i <- PlainRange(0, len))
                                        yield (IdealInt(Debug.random(-20, 20)),
                                               constsVarsOne(Debug.random(0, constsVarsOne.size)))

   def randomLC(len : Int) = LinearCombination(randomInput(len), to)

   def randomEqAC(eqNum : Int, maxEqSize : Int) : ArithConj = {
     val posEqNum = Debug.random(0, eqNum+1)
     randomEqAC(posEqNum, eqNum - posEqNum, maxEqSize)
   }

   def randomEqAC(posEqNum : Int, negEqNum : Int, maxEqSize : Int) : ArithConj = {
     val inputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                     .take(posEqNum).toList
     val eqConj = EquationConj(inputConj, to)
     val negInputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                        .take(negEqNum).toList
     val negEqConj = NegEquationConj(negInputConj, to)
     
     ArithConj(eqConj, negEqConj, InEqConj.TRUE, to)
   }

   def randomAC(eqNum : Int, maxEqSize : Int) : ArithConj = {
     val Seq(a,b) = Debug.randoms(0, eqNum+1).take(2).toList
     randomAC(a min b, (a - b).abs, eqNum - (a max b), maxEqSize)
   }

   def randomAC(posEqNum : Int, negEqNum : Int, inEqNum : Int, maxEqSize : Int) : ArithConj = {
     val inputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                     .take(posEqNum).toList
     val eqConj = EquationConj(inputConj, to)
     val negInputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                        .take(negEqNum).toList
     val negEqConj = NegEquationConj(negInputConj, to)
     val inInputConj = (for (len <- Debug.randoms(0, maxEqSize+1)) yield randomLC(len))
                        .take(inEqNum).toList
     val inEqConj = InEqConj(inInputConj, to)
     
     ArithConj(eqConj, negEqConj, inEqConj, to)
   }
   
   def randomEqConj(sizeFactor : Double,
                    maxEqNum : Int, maxEqSize : Int) : Conjunction =
     randomConj(sizeFactor,
                () => randomEqAC(Debug.random(0, maxEqNum),
                                 Debug.random(0, maxEqSize)))
   
   def randomConj(sizeFactor : Double,
                  maxEqNum : Int, maxEqSize : Int) : Conjunction =
     randomConj(sizeFactor,
                () => randomAC(Debug.random(0, maxEqNum),
                               Debug.random(0, maxEqSize)))
   
   private def randomConj(sizeFactor : Double, acGen : () => ArithConj) = {
     val quans : List[Quantifier] = (for (i <- Debug.randoms(0, 2))
                                     yield (if (i==0) Quantifier.ALL else Quantifier.EX))
                                    .take(Debug.random(0, 10)).toList
     val arithConj = acGen()
     val negConjs = if (arithConj.isFalse)
       NegatedConjunctions.TRUE
     else
       randomNegConjs(sizeFactor - 1, acGen)

     Conjunction(quans, arithConj, PredConj.TRUE, negConjs, to)
   }

   private def randomNegConjs(sizeFactor : Double, acGen : () => ArithConj) : NegatedConjunctions = {
     val conjs = for (_ <- PlainRange(0, Debug.random(0, 1 max sizeFactor.toInt)))
                 yield randomConj(sizeFactor, acGen)
     
     NegatedConjunctions(conjs, to)
   }

}
