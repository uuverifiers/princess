/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor;

import ap.util.{Debug, Logic, APTestCase, PlainRange, FilterIt}
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
   val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c, Set.empty))
   val toRev = (consts :\ TermOrder.EMPTY)((c, o) => o.extend(c, Set.empty))
   
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
