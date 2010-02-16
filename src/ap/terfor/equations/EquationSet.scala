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

package ap.terfor.equations;

import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Predicate, Atom}
import ap.basetypes.IdealInt
import ap.util.{Debug, Logic, Seqs}

object EquationSet {

  private val AC = Debug.AC_EQUATIONS
  
  
}

abstract class EquationSet protected (protected val lhss : Array[LinearCombination],
                                      val order : TermOrder)
               extends Formula with RandomAccessSeq[LinearCombination] {
  
  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(EquationSet.AC,
                   (
                     // as a special case, we allow a singleton set with a
                     // constant as element (to be able to express unsatisfiable
                     // conjunctions or valid disjunctions of equations properly)
                     size == 1 && (this(0) == LinearCombination.ZERO ||
                                   this(0) == LinearCombination.ONE) 
                     ||
                     // otherwise, only primitive elements are allowed
                     Logic.forall(for (lhs <- this.elements)
                                  yield (lhs.isPrimitive && lhs.isPositive))
                   )
                   &&
                   Logic.forall(0, this.size - 1,
                                (i:Int) => order.compare(this(i), this(i+1)) > 0)
                   &&
                   Logic.forall(for (lc <- this.elements) yield lc isSortedBy order))
  //////////////////////////////////////////////////////////////////////////////

  def length : Int = lhss.length
    
  def apply(i : Int) : LinearCombination = lhss(i)
  
  override def elements = lhss.elements

  def contains(lc : LinearCombination) : Boolean =
    // we first check the set of contained constants to avoid problems with
    // the <code>TermOrder</code>
    if (lc.constants subsetOf this.constants) {
      // in this case, binary search for the linear combination
      
      ////////////////////////////////////////////////////////////////////////
      Debug.assertPre(EquationSet.AC, lc isSortedBy order)
      ////////////////////////////////////////////////////////////////////////
      
      implicit def orderLC(thisLC : LinearCombination) =
        new Ordered[LinearCombination] {
          def compare(thatLC : LinearCombination) : Int =
            order.compare(thatLC, thisLC)
        }
      
      Seqs.binSearch(this, 0, this.size, lc) match {
      case Seqs.Found(_) => true
      case Seqs.NotFound(_) => false
      }
    } else {
      false
    }
  
  //////////////////////////////////////////////////////////////////////////////

  def toSet = new scala.collection.Set[LinearCombination] {
    def size = EquationSet.this.size
    def elements = EquationSet.this.elements
    def contains(lc : LinearCombination) = EquationSet.this contains lc
  }

  lazy val leadingTermSet : scala.collection.Set[Term] = {
    val res = new scala.collection.mutable.HashSet[Term]
    res ++= (for (lc <- this.elements) yield lc.leadingTerm)
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  def implies(that : EquationSet) : Boolean =
    // TODO: make this more efficient
    that forall (this contains _)
    
  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
    Set.empty ++ (for (lc <- this.elements; v <- lc.variables.elements) yield v)

  lazy val constants : Set[ConstantTerm] =
    Set.empty ++ (for (lc <- this.elements; c <- lc.constants.elements) yield c)
      
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
      val strings = for (lhs <- this.elements)
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
