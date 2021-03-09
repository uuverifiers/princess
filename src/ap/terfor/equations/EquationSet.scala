/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.equations;

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Predicate, Atom}
import ap.basetypes.IdealInt
import ap.util.{Debug, Logic, Seqs}

object EquationSet {

  private val AC = Debug.AC_EQUATIONS
  
  
}

abstract class EquationSet protected (protected val lhss : Array[LinearCombination],
                                      val order : TermOrder)
               extends Formula with IndexedSeq[LinearCombination] {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(EquationSet.AC,
                   (
                     // as a special case, we allow a singleton set with a
                     // constant as element (to be able to express unsatisfiable
                     // conjunctions or valid disjunctions of equations properly)
                     size == 1 && (this(0) == LinearCombination.ZERO ||
                                   this(0) == LinearCombination.ONE) 
                     ||
                     // otherwise, only primitive elements are allowed
                     (this forall { case lhs => lhs.isPrimitive && lhs.isPositive })
                   )
                   &&
                   Logic.forall(0, this.size - 1,
                                (i:Int) => order.compare(this(i), this(i+1)) > 0)
                   &&
                   (this forall (_ isSortedBy order)))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def length : Int = lhss.length
    
  def apply(i : Int) : LinearCombination = lhss(i)
  
  override def iterator = lhss.iterator

  def contains(lc : LinearCombination) : Boolean =
    // we first check the set of contained constants to avoid problems with
    // the <code>TermOrder</code>
    if (lc.constants subsetOf this.constants) {
      // in this case, binary search for the linear combination
      
      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
      Debug.assertPre(EquationSet.AC, lc isSortedBy order)
      //-END-ASSERTION-///////////////////////////////////////////////////////
      
      Seqs.binSearch(this, 0, this.size, lc)(order.reverseLCOrdering) match {
      case Seqs.Found(_) => true
      case Seqs.NotFound(_) => false
      }
    } else {
      false
    }
  
  //////////////////////////////////////////////////////////////////////////////

  def toSet = new scala.collection.Set[LinearCombination] {
    override def size = EquationSet.this.size
    def iterator = EquationSet.this.iterator
    def contains(lc : LinearCombination) = EquationSet.this contains lc
    def +(elem: LinearCombination) = throw new UnsupportedOperationException
    def -(elem: LinearCombination) = throw new UnsupportedOperationException
  }

  lazy val leadingTermSet : scala.collection.Set[Term] = {
    val res = new scala.collection.mutable.HashSet[Term]
    res ++= (for (lc <- this.iterator) yield lc.leadingTerm)
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  def implies(that : EquationSet) : Boolean =
    // TODO: make this more efficient
    that forall (this contains _)
    
  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
//    (for (lc <- this.iterator; v <- lc.variables.iterator) yield v).toSet
    (for (lc <- this.iterator; v <- lc.variablesIterator) yield v).toSet

  lazy val constants : Set[ConstantTerm] =
//    (for (lc <- this.iterator; c <- lc.constants.iterator) yield c).toSet
    (for (lc <- this.iterator; c <- lc.constantsIterator) yield c).toSet

  def predicates : Set[Predicate] = Set.empty

  def groundAtoms : Set[Atom] = Set.empty

  //////////////////////////////////////////////////////////////////////////////

  protected val relationString : String
  
  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val strings = for (lhs <- this.iterator)
                    yield ("" + lhs + " " + relationString + " 0")
      if (strings.hasNext)
        strings.reduceLeft((s1 : String, s2 : String) =>
                           s1 + " & " + s2)
      else
        throw new Error // should never be reached
    }
  }
  
  override def equals(that : Any) : Boolean = that match {
    case that : EquationSet => this.lhss sameElements that.lhss
    case _ => false
  }

  private lazy val hashCodeVal = Seqs.computeHashCode(this, 0, 3)

  override def hashCode = hashCodeVal
}
