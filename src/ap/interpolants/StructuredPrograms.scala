/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.parser.{ITerm, IFormula, IConstant, IFunApp, ConstantSubstVisitor}
import ap.parser.IExpression._
import ap.terfor.ConstantTerm

object StructuredPrograms {

  abstract sealed class StructuredProgram {
    def +(that : StructuredProgram) : StructuredProgram = Sequence(this, that)
    def |(that : StructuredProgram) : StructuredProgram = Choice(this, that)
  }
  
  abstract sealed class Statement extends StructuredProgram
  
  case class Assignment(lhs : ConstantTerm, rhs : ITerm) extends Statement
  case class Assumption(formula : IFormula) extends Statement
  case class Assertion(formula : IFormula) extends Statement
  
  case class Sequence(a : StructuredProgram,
                      b : StructuredProgram) extends StructuredProgram
  case class Choice  (a : StructuredProgram,
                      b : StructuredProgram) extends StructuredProgram

  //////////////////////////////////////////////////////////////////////////////
  
  object Assignment {
    def apply(lhs : ITerm, rhs : ITerm)
             (implicit voc : FrameworkVocabulary) : Assignment = {
      def simp(lhs : ITerm, rhs : ITerm) : (ConstantTerm, ITerm) = lhs match {
        case IConstant(c) => (c, rhs)
        case IFunApp(voc.select, List(ar, ind)) => simp(ar, voc.store(ar, ind, rhs))
      }
      val (newLhs, newRhs) = simp(lhs, rhs)
      Assignment(newLhs, newRhs)
    }
  }
  
  implicit def toRichTerm(t : ITerm)(implicit voc : FrameworkVocabulary) =
    new Object {
	  def apply(ind : ITerm) = voc.select(t, ind)
	  def apply(ind : ConstantTerm) = voc.select(t, ind)
      def := (rhs : ITerm) = Assignment(t, rhs)
    }

  def seq(stmts : StructuredProgram*) : StructuredProgram =
    stmts.reduceLeft(Sequence(_, _))
  
  def toRelation(prog : StructuredProgram,
                 in : Map[ConstantTerm, ConstantTerm],
                 step : Int)
                (implicit st : SigTracker)
                : (IFormula, Map[ConstantTerm, ConstantTerm]) = prog match {
    case Assignment(lhs, rhs) => {
      val c = st.cloneConst(lhs, "_" + step)
      (ConstantSubstVisitor.rename(rhs, in) === c, in + (lhs -> c))
    }
  }
  
}
