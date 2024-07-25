/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2019 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.arithconj.ArithConj
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.util.{Debug, Logic, Seqs, Timeout}

object NegatedConjunctions {
  
  val AC = Debug.AC_PROP_CONNECTIVES

  def apply(conj : Conjunction, order : TermOrder) : NegatedConjunctions =
    apply(Iterator.single(conj), order)
  
  def apply(conjs : Iterable[Conjunction], order : TermOrder)
                                                : NegatedConjunctions =
    apply(conjs.iterator, order)

  def apply(conjs : Iterator[Conjunction], order : TermOrder)
                                                : NegatedConjunctions = {
    var compareCnt = 0
    def compareConjs(c1 : Conjunction, c2 : Conjunction) = {
      compareCnt = compareCnt + 1
      if (compareCnt % 100 == 0)
        Timeout.check
      Conjunction.compare(c1, c2, order) > 0
    }

    Seqs.filterAndSort[Conjunction](conjs, c => c.isFalse, c => c.isTrue,
                                    c => c, compareConjs _) match {
      case Seqs.FilteredSorted(sortedConjs) => {
        val contractedConjs = Seqs.removeDuplicates(sortedConjs).toArray
        new NegatedConjunctions (contractedConjs, order)
      }
      case Seqs.FoundBadElement(_) => FALSE
    }
  }

  val TRUE : NegatedConjunctions =
    new NegatedConjunctions (Array(), TermOrder.EMPTY)

  lazy val FALSE : NegatedConjunctions =
    new NegatedConjunctions (Array(Conjunction.TRUE), TermOrder.EMPTY)
  
}

/**
 * Class for representing a conjunction of negated <code>Conjunction</code>s.
 */
class NegatedConjunctions private (private val conjs : Array[Conjunction],
                                   val order : TermOrder) 
                          extends Formula with SortedWithOrder[NegatedConjunctions]
                                          with IndexedSeq[Conjunction] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(NegatedConjunctions.AC,
                   Logic.forall(for (conj <- this.iterator)
                                yield ((conj isSortedBy order) && !conj.isFalse))
                   &&
                   (
                     // to be able to represent <code>NegatedConjunctions.FALSE</code>,
                     // we allow singleton conjunctions whose only conjunct is true
                     this.size == 1 && this(0) == Conjunction.TRUE
                     ||
                     Logic.forall(for (conj <- this.iterator) yield !conj.isTrue)
                   )
                   &&
                   Logic.forall(0, conjs.size - 1,
                                (i) => Conjunction.compare
                                        (conjs(i), conjs(i+1), order) > 0)
                 )
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : NegatedConjunctions = {
    if (isSortedBy(newOrder)) {
      this
    } else {
      NegatedConjunctions(for (conj <- this.iterator) yield (conj sortBy newOrder),
                          newOrder)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def length : Int = conjs.length
   
  def apply(i : Int) : Conjunction = conjs(i)
   
  def elements = conjs.iterator

  //////////////////////////////////////////////////////////////////////////////

  def update(newConjs : Iterable[Conjunction],
             newOrder : TermOrder) : NegatedConjunctions =
    if (Seqs.identicalSeqs(this, newConjs))
      this
    else
      NegatedConjunctions(newConjs, newOrder)
  
  def updateSubset(newConjs : Iterable[Conjunction],
                   newOrder : TermOrder) : NegatedConjunctions =
    if (this.size == newConjs.size)
      this
    else
      new NegatedConjunctions(newConjs.toArray, newOrder)

  def &(that : NegatedConjunctions)
       (implicit newOrder : TermOrder) : NegatedConjunctions =
    if (that.isEmpty)
      this
    else
      NegatedConjunctions.apply(this.iterator ++ that.iterator, newOrder)
  
  //////////////////////////////////////////////////////////////////////////////

  def implies(that : NegatedConjunctions) : Boolean =
    // TODO: make this more efficient
    ((that diff this) _2).isEmpty
    
  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
    Set.empty ++ (for (conj <- conjs.iterator; v <- conj.variables.iterator) yield v)

  lazy val constants : Set[ConstantTerm] =
    Set.empty ++ (for (conj <- conjs.iterator; c <- conj.constants.iterator) yield c)

  lazy val predicates : Set[Predicate] =
    Set.empty ++ (for (conj <- conjs.iterator; p <- conj.predicates.iterator) yield p)

  lazy val groundAtoms : Set[Atom] =
    Set.empty ++ (for (conj <- conjs.iterator; g <- conj.groundAtoms.iterator) yield g)

  //////////////////////////////////////////////////////////////////////////////

  def isTrue : Boolean = (this.isEmpty)

  def isFalse : Boolean = (!this.isEmpty && this(0).isTrue)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find the subset of conjuncts in this conjunction that also occur in
   * <code>oldConj</code>, as well as the subset of conjuncts that do not occur
   * in <code>oldConj</code>.
   */
  def diff(oldConj : NegatedConjunctions)
                        : (NegatedConjunctions, NegatedConjunctions) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(NegatedConjunctions.AC, oldConj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    implicit val orderConjunctions = Conjunction.conjOrdering(order)

    val (unchanged, changed) = Seqs.diff(this, oldConj)
    (this.updateSubset(unchanged, order), this.updateSubset(changed, order))
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Remove some negated conjunctions.
   */
  def --(that : NegatedConjunctions) : NegatedConjunctions =
    if (that.isTrue)
      this
    else
      (this diff that)._2

  /**
   * Add a further negated conjunction.
   */
  def +(that : Conjunction)
       (implicit order : TermOrder) : NegatedConjunctions = {
    val N = this.size
    if (N == 0) {
      new NegatedConjunctions(Array(that), order)
    } else {
      implicit val revConjOrder = Conjunction reverseConjOrdering order
      Seqs.binSearch(conjs, 0, N, that) match {
        case Seqs.Found(_) =>
          this
        case Seqs.NotFound(i) => {
          val newConjs = new Array[Conjunction] (N + 1)
          Array.copy(conjs, 0, newConjs, 0, i)
          newConjs(i) = that
          Array.copy(conjs, i, newConjs, i + 1, N - i)
          new NegatedConjunctions(newConjs, order)
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def containsLiteral : Boolean =
    Logic.exists(for (conj <- this.iterator) yield conj.isLiteral)

  def containsNegatedConjunction : Boolean =
    Logic.exists(for (conj <- this.iterator) yield conj.isNegatedConjunction)
    
  def isNegatedQuantifiedConjunction : Boolean =
    (this.size == 1 && !this(0).quans.isEmpty)
    
  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val strings = for (conj <- this.iterator) yield ("! " + conj)
      if (strings.hasNext)
        strings.reduceLeft((s1 : String, s2 : String) =>
                           s1 + " & " + s2)
      else
        throw new Error // should never be reached
    }
  }

  override def equals(that : Any) : Boolean = that match {
    case that : NegatedConjunctions => this.conjs sameElements that.conjs
    case _ => false
  }
  
  private lazy val hashCodeVal = Seqs.computeHashCode(this, 9871621, 5)

  override def hashCode = hashCodeVal

}
