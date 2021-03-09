/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010,2011 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.parser.{ITerm, IFormula, IConstant, IFunApp, ConstantSubstVisitor,
                  IBinJunctor}
import ap.parser.IExpression._
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate

object StructuredPrograms {

  abstract sealed class StructuredProgram {
    def +(that : StructuredProgram) : StructuredProgram = (this, that) match {
      case (Skip, x) => x
      case (x, Skip) => x
      case _ => Sequence(this, that)
    }
    def |(that : StructuredProgram) : StructuredProgram = (this, that) match {
      case (Skip, Skip) => Skip
      case _ => Choice(this, that)
    }
  }
  
  abstract sealed class Statement extends StructuredProgram
  
  object Skip extends Statement {
    override def toString = "Skip"
  }
  case class Assignment(lhs : ConstantTerm, rhs : ITerm) extends Statement {
    override def toString = "" + lhs + " := " + rhs
  }
  case class Assumption(formula : IFormula) extends Statement
  case class Assertion(formula : IFormula) extends Statement
  
  case class Sequence(a : StructuredProgram,
                      b : StructuredProgram) extends StructuredProgram {
    override def toString = "" + a + " + " + b
  }
  case class Choice  (a : StructuredProgram,
                      b : StructuredProgram) extends StructuredProgram {
    override def toString = "((" + a + ") | (" + b + "))"
  }

  //////////////////////////////////////////////////////////////////////////////
  
  object Assignment {
    def apply(lhs : ITerm, rhs : ITerm)
             (implicit voc : FrameworkVocabulary) : Assignment = {
      def simp(lhs : ITerm, rhs : ITerm) : (ConstantTerm, ITerm) = lhs match {
        case IConstant(c) => (c, rhs)
        case IFunApp(voc.select, Seq(ar, ind)) => simp(ar, voc.store(ar, ind, rhs))
      }
      val (newLhs, newRhs) = simp(lhs, rhs)
      Assignment(newLhs, newRhs)
    }
  }

  class RichTerm(t : ITerm)(implicit voc : FrameworkVocabulary) {
	def apply(ind : ITerm) = voc.select(t, ind)
	def apply(ind : ConstantTerm) = voc.select(t, ind)
    def := (rhs : ITerm) = Assignment(t, rhs)
  }
  
  implicit def toRichTerm(t : ITerm)
                         (implicit voc : FrameworkVocabulary) = new RichTerm (t)

  implicit def toRichTerm(c : ConstantTerm)
                         (implicit voc : FrameworkVocabulary) = new RichTerm (c)

  def seq(stmts : StructuredProgram*) : StructuredProgram =
    stmts.reduceLeft(Sequence(_, _))

  //////////////////////////////////////////////////////////////////////////////

  def equalStates(stateVars : Iterable[ConstantTerm],
                  inst1 : Renaming, inst2 : Renaming) : IFormula =
    connect(for (c <- stateVars.iterator) yield (inst1(c) === inst2(c)),
            IBinJunctor.And)
  
  //////////////////////////////////////////////////////////////////////////////
  // Weakest precondition computation
  
  type Renaming = Map[ConstantTerm, ConstantTerm]
  
  def assignedVars(prog : StructuredProgram) : Set[ConstantTerm] = prog match {
    case Assignment(c, _) => Set(c)
    case Sequence(a, b) => assignedVars(a) ++ assignedVars(b)
    case Choice(a, b) => assignedVars(a) ++ assignedVars(b)
    case _ => Set()
  }
  
  def wp(prog : StructuredProgram, in : Renaming,
         post : (Renaming => (IFormula, Renaming)))
        (implicit st : SigTracker) : (IFormula, Renaming) = {
    import ConstantSubstVisitor.rename

    prog match {
      case Skip =>
        post(in)
      
      case Assignment(lhs, rhs) => {
        val c = st.cloneConst(in(lhs), "_n")
        val (p, out) = post(in + (lhs -> c))
        ((rename(rhs, in) === c) ===> p, out)
      }
      
      case Assumption(formula) => {
        val (p, out) = post(in)
        (rename(formula, in) ===> p, out)
      }
      
      case Assertion(formula) => {
        val (p, out) = post(in)
        (rename(formula, in) &&& p, out)
      }
      
      case Sequence(a, b) =>
        wp(a, in, wp(b, _, post))
        
      case Choice(a, b) => {
        val assignable = st.sig.order sort assignedVars(prog)
        val newVars = Map() ++
          (for (c <- assignable.iterator) yield (c -> st.cloneConst(in(c), "_i")))

        val (cont, out) = post(in ++ newVars)
        
        val p = new Predicate ("p" + st.sig.order.orderedPredicates.size, 0)
        st addPred p
        
        def localPost(r : Renaming) =
          (equalStates(assignable, r, newVars) ===> p(), r)
        
        (((wp(a, in, localPost _) _1) &&& (wp(b, in, localPost _) _1))
         |||
         (!p() &&& cont),
         out)
      }
    }
  }
  
}
