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

package ap.terfor.arithconj;

import scala.collection.mutable.ArrayBuffer

import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithEqs}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.{Predicate, Atom}
import ap.util.{Debug, Logic}

object ArithConj {
  
  val AC = Debug.AC_PROP_CONNECTIVES
  
  def apply(positiveEqs : EquationConj, negativeEqs : NegEquationConj,
            inEqs : InEqConj, order : TermOrder) : ArithConj = {
    if (positiveEqs.isFalse || negativeEqs.isFalse || inEqs.isFalse)
      FALSE
    else if (positiveEqs.isTrue && negativeEqs.isTrue && inEqs.isTrue)
      TRUE
    else
      new ArithConj (positiveEqs, negativeEqs, inEqs, order)
  }
  
  def unapply(conj : ArithConj) : Option[(EquationConj, NegEquationConj, InEqConj)] =
    Some(conj.positiveEqs, conj.negativeEqs, conj.inEqs)
  
  val TRUE : ArithConj = new ArithConj(EquationConj.TRUE, NegEquationConj.TRUE,
                                       InEqConj.TRUE, TermOrder.EMPTY)

  val FALSE : ArithConj = new ArithConj(EquationConj.FALSE, NegEquationConj.TRUE,
                                        InEqConj.TRUE, TermOrder.EMPTY)
                                        
  /**
   * Compute the conjunction of equations, inequations and inequalities.
   */
  def conj(conjs : Iterator[Formula],
           logger : ComputationLogger,
           order : TermOrder) : ArithConj = {
    val posEqs = new ArrayBuffer[EquationConj]
    val negEqs = new ArrayBuffer[NegEquationConj]
    val inEqs = new ArrayBuffer[InEqConj]
    
    for (conj <- conjs) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, order isSortingOf conj)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      conj match {
      case conj : EquationConj => posEqs += conj
      case conj : NegEquationConj => negEqs += conj
      case conj : InEqConj => inEqs += conj
      case conj : ArithConj => {
        posEqs += conj.positiveEqs
        negEqs += conj.negativeEqs
        inEqs += conj.inEqs
      }
      }
    }
    
    apply(EquationConj.conj(posEqs, logger, order),
          NegEquationConj.conj(negEqs, order),
          InEqConj.conj(inEqs.elements, logger, order),
          order)
  }

  def conj(conjs : Iterator[Formula],
           order : TermOrder) : ArithConj =
    conj(conjs, ComputationLogger.NonLogger, order)

  def conj(conjs : Iterable[Formula], order : TermOrder) : ArithConj =
    conj(conjs.elements, order)

  def conj(f : Formula, order : TermOrder) : ArithConj = conj(List(f), order)

}

/**
 * The class for a conjunction of equations, negated equations and inequalities
 */
class ArithConj private (val positiveEqs : EquationConj,
                         val negativeEqs : NegEquationConj,
                         val inEqs : InEqConj,
                         val order : TermOrder)
                extends Formula with SortedWithOrder[ArithConj] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ArithConj.AC,
                   (positiveEqs isSortedBy order) &&
                   (negativeEqs isSortedBy order) &&
                   (inEqs isSortedBy order) &&
                   !negativeEqs.isFalse && !inEqs.isFalse)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : ArithConj = {
    if (isSortedBy(newOrder)) {
      this
    } else {
      ArithConj (positiveEqs sortBy newOrder,
                 negativeEqs sortBy newOrder,
                 inEqs sortBy newOrder,
                 newOrder)
    }
  }
   
  //////////////////////////////////////////////////////////////////////////////

  def isTrue : Boolean = (positiveEqs.isTrue && negativeEqs.isTrue && inEqs.isTrue)

  def isFalse : Boolean = (positiveEqs.isFalse || negativeEqs.isFalse || inEqs.isFalse)

  def size : Int = (positiveEqs.size + negativeEqs.size + inEqs.size)
  
  def isEmpty : Boolean = size == 0

  def elements : Iterator[ArithConj] =
    (for (eq <- positiveEqs.elements) yield ArithConj(EquationConj(eq, order),
                                                      NegEquationConj.TRUE,
                                                      InEqConj.TRUE,
                                                      order)) ++
    (for (eq <- negativeEqs.elements) yield ArithConj(EquationConj.TRUE,
                                                      NegEquationConj(eq, order),
                                                      InEqConj.TRUE,
                                                      order)) ++
    (for (eq <- inEqs.elements) yield ArithConj(EquationConj.TRUE,
                                                NegEquationConj.TRUE,
                                                InEqConj(eq, order),
                                                order))

  /**
   * Return whether this conjunction actually only is a single literal
   */
  def isLiteral : Boolean = (this.size == 1)

  /**
   * Create the negation of at most one equation
   */
  def negate : ArithConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ArithConj.AC, this.size <= 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (!negativeEqs.isEmpty) {
      ArithConj(negativeEqs.negate, NegEquationConj.TRUE, InEqConj.TRUE, order)
    } else if (!positiveEqs.isEmpty) {
      ArithConj(EquationConj.TRUE, positiveEqs.negate, InEqConj.TRUE, order)
    } else if (!inEqs.isEmpty) {
      ArithConj(EquationConj.TRUE, NegEquationConj.TRUE, inEqs.negate, order)
    } else {
      ArithConj.FALSE
    }
  }

  /**
   * Update the positive equations of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updatePositiveEqs(newEqs : EquationConj)(implicit newOrder : TermOrder)
                       : ArithConj =
    if (this.positiveEqs == newEqs)
      this
    else
      ArithConj(newEqs, this.negativeEqs, this.inEqs, newOrder)
  
  /**
   * Update the Negative equations of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateNegativeEqs(newEqs : NegEquationConj)(implicit newOrder : TermOrder)
                       : ArithConj =
    if (this.negativeEqs == newEqs)
      this
    else
      ArithConj(this.positiveEqs, newEqs, this.inEqs, newOrder)

  /**
   * Update the inequalities of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateInEqs(newInEqs : InEqConj)(implicit newOrder : TermOrder) : ArithConj =
    if (this.inEqs == newInEqs)
      this
    else
      ArithConj(this.positiveEqs, this.negativeEqs, newInEqs, newOrder)

  //////////////////////////////////////////////////////////////////////////////

  def implies(that : ArithConj) : Boolean =
    (this.positiveEqs implies that.positiveEqs) &&
    (this.negativeEqs implies that.negativeEqs) &&
    (this.inEqs implies that.inEqs)
        
  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
    positiveEqs.variables ++ negativeEqs.variables ++ inEqs.variables
    
  lazy val constants : Set[ConstantTerm] =
    positiveEqs.constants ++ negativeEqs.constants ++ inEqs.constants
      
  def predicates : Set[Predicate] = Set.empty

  def groundAtoms : Set[Atom] = Set.empty

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val strings = (for (lhs <- positiveEqs.elements) yield ("" + lhs + " = 0")) ++
                    (for (lhs <- negativeEqs.elements) yield ("" + lhs + " != 0")) ++
                    (for (lhs <- inEqs.elements) yield ("" + lhs + " >= 0"))
      if (strings.hasNext)
        strings.reduceLeft((s1 : String, s2 : String) => s1 + " & " + s2)
      else
        throw new Error // should never be reached
    }
  }

  override def equals(that : Any) : Boolean = that match {
    case that : ArithConj => this.positiveEqs == that.positiveEqs &&
                             this.negativeEqs == that.negativeEqs &&
                             this.inEqs == that.inEqs
    case _ => false
  }

  override def hashCode = (positiveEqs.hashCode +
                           726327 * negativeEqs.hashCode +
                           36323 * inEqs.hashCode)
}
