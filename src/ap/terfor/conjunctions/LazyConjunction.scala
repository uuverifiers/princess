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

package ap.terfor.conjunctions

import ap.terfor.{TermOrder, Formula}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.PredConj
import ap.util.{Debug, Logic, Seqs}

object LazyConjunction {

  protected[conjunctions] val AC = Debug.AC_PROP_CONNECTIVES

  val TRUE : LazyConjunction =
    AtomicLazyConjunction(Conjunction.TRUE, TermOrder.EMPTY)
  val FALSE : LazyConjunction =
    AtomicLazyConjunction(Conjunction.FALSE, TermOrder.EMPTY)
  
  def apply(conj : Formula)(implicit order : TermOrder) : LazyConjunction =
    AtomicLazyConjunction(conj, order)
    
  def conj(formulas : Iterator[LazyConjunction])
          (implicit order : TermOrder) : LazyConjunction =
    (TRUE.asInstanceOf[LazyConjunction] /: formulas) (_ & _)
  
  def conj(formulas : Iterable[LazyConjunction])
          (implicit order : TermOrder) : LazyConjunction =
    conj(formulas.iterator)

  def disj(formulas : Iterator[LazyConjunction])
          (implicit order : TermOrder) : LazyConjunction =
    conj(formulas map (_.negate)).negate
  
  def disj(formulas : Iterable[LazyConjunction])
          (implicit order : TermOrder) : LazyConjunction =
    disj(formulas.iterator)
}

/**
 * A lazy version of conjunctions. This class can be useful when recursively
 * constructing large formulae, since the number of invocations of methods of
 * the class <code>Conjunction</code> is reduced.
 */
abstract sealed class LazyConjunction {

  def toFormula : Formula
  def toConjunction : Conjunction
  
  def negate : LazyConjunction = NegLazyConjunction(this)

  def isTrue : Boolean = false
  def isFalse : Boolean = false
  
  def unary_! : LazyConjunction = this.negate
  
  protected[conjunctions] def forceAnd : LazyConjunction =
    this
  protected[ap] def order : TermOrder =
    throw new UnsupportedOperationException
  
  def &(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction
  
  def |(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this.negate & that.negate).negate

  def ==>(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this & that.negate).negate

  def <=>(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this ==> that) & (that ==> this)
  
}

////////////////////////////////////////////////////////////////////////////////

protected[conjunctions] case class AtomicLazyConjunction(form : Formula,
                                                         newOrder : TermOrder)
                             extends LazyConjunction {

  def toFormula : Formula = form
  
  def toConjunction : Conjunction = form match {
    case conj : Conjunction => conj
    case _                  => Conjunction.conj(form, newOrder)
  }

  override def isTrue : Boolean = form.isTrue
  override def isFalse : Boolean = form.isFalse

  protected[ap] override def order : TermOrder = newOrder

  override def &(that : LazyConjunction)
                (implicit newOrder : TermOrder) : LazyConjunction =
    if (form.isFalse)
      LazyConjunction.FALSE
    else if (form.isTrue)
      that
    else {
      val forcedThat = that.forceAnd
      if (forcedThat.isFalse)
        LazyConjunction.FALSE
      else if (forcedThat.isTrue)
        this
      else
        AndLazyConjunction(this, forcedThat, newOrder)
    }

  override def negate : LazyConjunction =
    if (form.isTrue)
      LazyConjunction.FALSE
    else if (form.isFalse)
      LazyConjunction.TRUE
    else
      NegLazyConjunction(this)

}

////////////////////////////////////////////////////////////////////////////////

protected[conjunctions] case class NegLazyConjunction(conj : LazyConjunction)
                             extends LazyConjunction {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LazyConjunction.AC,
                   (conj match {
                     case _ : AtomicLazyConjunction | _ : AndLazyConjunction => true
                     case _ => false
                    }) &&
                   !conj.isTrue && !conj.isFalse)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  protected[ap] override def order : TermOrder = conj.order

  def toFormula : Formula = conj match {
    case AtomicLazyConjunction(eqs : EquationConj, _)
      if (eqs.size <= 1) => eqs.negate
    case AtomicLazyConjunction(eqs : NegEquationConj, _)
      if (eqs.size <= 1) => eqs.negate
    case AtomicLazyConjunction(inEqs : InEqConj, _)
      if (inEqs.size <= 1) => inEqs.negate
    case AtomicLazyConjunction(pred : PredConj, _)
      if (pred.isLiteral) => pred.negate
    case _ =>
      conj.toConjunction.negate
  }
  
  def toConjunction : Conjunction = toFormula match {
    case c : Conjunction => c
    case f => Conjunction.conj(f, conj.order)
  }

  override def negate : LazyConjunction = conj

  def &(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction = {
    val form = toFormula
    if (form.isFalse)
      LazyConjunction.FALSE
    else if (form.isTrue)
      that
    else {
      val forcedThat = that.forceAnd
      if (forcedThat.isFalse)
        LazyConjunction.FALSE
      else if (forcedThat.isTrue)
        this
      else
        AndLazyConjunction(AtomicLazyConjunction(form, newOrder),
                           forcedThat, newOrder)
    }
  }

  override protected[conjunctions] def forceAnd : LazyConjunction =
    AtomicLazyConjunction(toFormula, conj.order)

}

////////////////////////////////////////////////////////////////////////////////

protected[conjunctions] case class AndLazyConjunction(
                                     left : LazyConjunction,
                                     right : LazyConjunction,
                                     newOrder : TermOrder)
                             extends LazyConjunction with Iterable[Formula] {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LazyConjunction.AC,
                   (left match {
                     case _ : AtomicLazyConjunction |
                          _ : AndLazyConjunction => true
                     case _ => false
                    }) &&
                   (right match {
                     case _ : AtomicLazyConjunction |
                          _ : AndLazyConjunction => true
                     case _ => false
                    }) &&
                   !left.isTrue && !left.isFalse && !right.isTrue && !right.isFalse)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def toFormula : Formula = toConjunction
                   
  def toConjunction : Conjunction = Conjunction.conj(iterator, newOrder)

  protected[ap] override def order : TermOrder = newOrder

  def &(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction = {
    val forcedThat = that.forceAnd
    if (forcedThat.isFalse)
      LazyConjunction.FALSE
    else if (forcedThat.isTrue)
      this
    else
      AndLazyConjunction(this, forcedThat, newOrder)
  }

  def iterator = new Iterator[Formula] {
    private var tree : LazyConjunction = AndLazyConjunction.this
    
    def hasNext = (tree != null)
    
    def next : Formula = tree match {
      case AtomicLazyConjunction(f, _) => {
        tree = null
        f
      }
      case AndLazyConjunction(AtomicLazyConjunction(f, _), r, _) => {
        tree = r
        f
      }
      case AndLazyConjunction(l, AtomicLazyConjunction(f, _), _) => {
        tree = l
        f
      }
      case AndLazyConjunction(AndLazyConjunction(l2, r2, _), r, o) => {
        tree = AndLazyConjunction(l2, AndLazyConjunction(r2, r, o), o)
        next
      }
      case _ => {
        assert(false)
        null
      }
    }
  }

}
