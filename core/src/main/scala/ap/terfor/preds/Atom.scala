/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.preds;

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.util.{Debug, Logic, Seqs}

object Atom {
  
  private val AC = Debug.AC_PREDICATES

  def apply(pred : Predicate,
            args : Iterator[LinearCombination],
            order : TermOrder) : Atom =
    new Atom (pred, Seqs toArray args, order)

  def apply(pred : Predicate,
            args : Iterable[LinearCombination],
            order : TermOrder) : Atom =
    new Atom (pred, args.toArray[LinearCombination], order)

  def unapply(f : Formula)
             : Option[(Predicate,
                       Seq[LinearCombination],
                       TermOrder)] = f match {
    case a : Atom => Some((a.pred, a, a.order))
    case _ => None
  }

  def createNoCopy(pred : Predicate,
                   args : Array[LinearCombination],
                   order : TermOrder) : Atom =
    new Atom (pred, args, order)

  /**
   * Assuming that the given predicates encode functions, check whether the
   * arguments (apart from the last argument, the function result) coincide,
   * and whether the predicates are the same
   */
  def sameFunctionApp(a : Atom, b : Atom) =
    a.pred == b.pred &&
    ((0 until (a.length - 1)) forall { case i => a(i) == b(i) })

}

class Atom private (val pred : Predicate,
                    args : IndexedSeq[LinearCombination],
                    val order : TermOrder)
      extends Formula
              with SortedWithOrder[Atom]
              with IndexedSeq[LinearCombination] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Atom.AC,
                   args.size == pred.arity &&
                   Logic.forall(for (lc <- this.iterator) yield (lc isSortedBy order)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  /**
   * Derive equations that describe under which condition this atom describes
   * the same location as that atom (basically, all the argument term have to
   * have the same values)
   */
  def unify(that : Atom, order : TermOrder) : EquationConj =
    if (this.pred == that.pred) {
      if (this.size == 0)
        // no arguments to compare
        EquationConj.TRUE
      else
        EquationConj(unificationConditions(that, order), order)
    } else {
      EquationConj.FALSE
    }
    
  def unificationConditions(that : Atom, order : TermOrder) : Iterator[LinearCombination] = {
    implicit val o = order
    for ((arg1, arg2) <- this.iterator zip that.iterator) yield (arg1 - arg2)
  }
  
  //////////////////////////////////////////////////////////////////////////////
    
  def length : Int = args.length
      
  def apply(i : Int) : LinearCombination = args(i)
  
  def elements = args.iterator

  def updateArgs(newArgs : Iterable[LinearCombination])
                (implicit order : TermOrder) : Atom =
    if (this sameElements newArgs)
      this
    else
      Atom(pred, newArgs, order)
  
  //////////////////////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : Atom =
    if (isSortedBy(newOrder))
      this
    else
      new Atom (pred,
                (for (a <- args)
                 yield (a sortBy newOrder)).toArray[LinearCombination],
                newOrder)
  
  //////////////////////////////////////////////////////////////////////////////
  
  lazy val variables : Set[VariableTerm] =
//    (for (lc <- this.iterator; v <- lc.variables.iterator) yield v).toSet
    (for (lc <- this.iterator; v <- lc.variablesIterator) yield v).toSet

  lazy val constants : Set[ConstantTerm] =
//    (for (lc <- this.iterator; c <- lc.constants.iterator) yield c).toSet
    (for (lc <- this.iterator; c <- lc.constantsIterator) yield c).toSet

  val predicates : Set[Predicate] = Set(pred)

  lazy val groundAtoms : Set[Atom] =
    if (variables.isEmpty) Set(this) else Set.empty

  /** Return <code>true</code> if this formula is obviously always true */
  def isTrue : Boolean = false
      
  /** Return <code>true</code> if this formula is obviously always false */
  def isFalse : Boolean = false

  //////////////////////////////////////////////////////////////////////////////

  override def equals(that : Any) : Boolean = that match {
    case that : Atom => (this.pred == that.pred) && (this sameElements that)
    case _ => false
  }
    
  private lazy val hashCodeVal =
    pred.hashCode + Seqs.computeHashCode(this, 911887, 9)

  override def hashCode = hashCodeVal

  override def toString = {
    val strings = for (lc <- this.iterator) yield lc.toString
    pred.name +
    (if (strings.hasNext)
       "(" + strings.reduceLeft((s1 : String, s2 : String) => s1 + ", " + s2) + ")"
     else
       "")
  }

}
