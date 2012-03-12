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

package ap.terfor.conjunctions

import ap.terfor.TermOrder
import ap.util.{Debug, Logic, Seqs}

object LazyConjunction {

  protected[conjunctions] val AC = Debug.AC_PROP_CONNECTIVES

  val TRUE  = AtomicLazyConjunction(Conjunction.TRUE)
  val FALSE = AtomicLazyConjunction(Conjunction.FALSE)
  
  def apply(conj : Conjunction) : LazyConjunction =
    AtomicLazyConjunction(conj)
    
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

  def toConjunction : Conjunction
  
  def negate : LazyConjunction = NegLazyConjunction(this)

  def isTrue : Boolean = false
  def isFalse : Boolean = false
  
  def unary_! : LazyConjunction = this.negate
  
  protected[conjunctions] def forceAnd : LazyConjunction = this
  
  def &(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    if (that.isFalse)
      LazyConjunction.FALSE
    else if (that.isTrue)
      this
    else
      AndLazyConjunction(this.forceAnd, that.forceAnd, newOrder)
  
  def |(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this.negate & that.negate).negate

  def ==>(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this & that.negate).negate

  def <=>(that : LazyConjunction)(implicit newOrder : TermOrder) : LazyConjunction =
    (this ==> that) & (that ==> this)
  
}

////////////////////////////////////////////////////////////////////////////////

protected[conjunctions] case class AtomicLazyConjunction(conj : Conjunction)
                             extends LazyConjunction {

  def toConjunction : Conjunction = conj

  override def isTrue : Boolean = conj.isTrue
  override def isFalse : Boolean = conj.isFalse

  override def &(that : LazyConjunction)
                (implicit newOrder : TermOrder) : LazyConjunction =
    if (this.isFalse || that.isFalse)
      LazyConjunction.FALSE
    else if (this.isTrue)
      that
    else if (that.isTrue)
      this
    else
      AndLazyConjunction(this.forceAnd, that.forceAnd, newOrder)

  override def negate : LazyConjunction =
    if (conj.isTrue)
      LazyConjunction.FALSE
    else if (conj.isFalse)
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

  def toConjunction : Conjunction = conj.toConjunction.negate

  override def negate : LazyConjunction = conj

  override protected[conjunctions] def forceAnd : LazyConjunction =
    AtomicLazyConjunction(toConjunction)

}

////////////////////////////////////////////////////////////////////////////////

protected[conjunctions] case class AndLazyConjunction(
                                     left : LazyConjunction,
                                     right : LazyConjunction,
                                     newOrder : TermOrder)
                             extends LazyConjunction with Iterable[Conjunction] {
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
  
  def toConjunction : Conjunction = Conjunction.conj(iterator, newOrder)
    
  def iterator = new Iterator[Conjunction] {
    private var tree : LazyConjunction = AndLazyConjunction.this
    
    def hasNext = (tree != null)
    
    def next : Conjunction = tree match {
      case AtomicLazyConjunction(c) => {
        tree = null
        c
      }
      case AndLazyConjunction(AtomicLazyConjunction(c), r, _) => {
        tree = r
        c
      }
      case AndLazyConjunction(l, AtomicLazyConjunction(c), _) => {
        tree = l
        c
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