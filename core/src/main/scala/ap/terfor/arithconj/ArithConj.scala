/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.arithconj;

import scala.collection.mutable.ArrayBuffer

import ap.terfor._
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
          InEqConj.conj(inEqs.iterator, logger, order),
          order)
  }

  def conj(conjs : Iterator[Formula],
           order : TermOrder) : ArithConj =
    conj(conjs, ComputationLogger.NonLogger, order)

  def conj(conjs : Iterable[Formula], order : TermOrder) : ArithConj =
    conj(conjs.iterator, order)

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

  def iterator : Iterator[ArithConj] =
    (for (eq <- positiveEqs.iterator) yield ArithConj(EquationConj(eq, order),
                                                      NegEquationConj.TRUE,
                                                      InEqConj.TRUE,
                                                      order)) ++
    (for (eq <- negativeEqs.iterator) yield ArithConj(EquationConj.TRUE,
                                                      NegEquationConj(eq, order),
                                                      InEqConj.TRUE,
                                                      order)) ++
    (for (eq <- inEqs.iterator) yield ArithConj(EquationConj.TRUE,
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
    if (this.positiveEqs eq newEqs)
      this
    else
      ArithConj(newEqs, this.negativeEqs, this.inEqs, newOrder)
  
  /**
   * Update the Negative equations of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateNegativeEqs(newEqs : NegEquationConj)(implicit newOrder : TermOrder)
                       : ArithConj =
    if (this.negativeEqs eq newEqs)
      this
    else
      ArithConj(this.positiveEqs, newEqs, this.inEqs, newOrder)

  /**
   * Update the inequalities of this conjunction (without changing anything
   * else apart from the <code>TermOrder</code>) 
   */
  def updateInEqs(newInEqs : InEqConj)(implicit newOrder : TermOrder) : ArithConj =
    if (this.inEqs eq newInEqs)
      this
    else
      ArithConj(this.positiveEqs, this.negativeEqs, newInEqs, newOrder)

  //////////////////////////////////////////////////////////////////////////////

  def implies(that : ArithConj) : Boolean =
    (this.positiveEqs implies that.positiveEqs) &&
    (this.negativeEqs implies that.negativeEqs) &&
    (this.inEqs implies that.inEqs)
        
  //////////////////////////////////////////////////////////////////////////////

  def --(that : ArithConj) : ArithConj =
    remove(that, ComputationLogger.NonLogger)

  def remove(that : ArithConj,
             logger : ComputationLogger) : ArithConj = {
    val newPE = this.positiveEqs -- that.positiveEqs
    val newNE = this.negativeEqs -- that.negativeEqs
    val newIE = this.inEqs.remove(that.inEqs, logger)

    if ((newPE eq this.positiveEqs) &&
        (newNE eq this.negativeEqs) &&
        (newIE eq this.inEqs))
      this
    else
      ArithConj(newPE, newNE, newIE, order)
  }

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
      val strings = (for (lhs <- positiveEqs.iterator) yield ("" + lhs + " = 0")) ++
                    (for (lhs <- negativeEqs.iterator) yield ("" + lhs + " != 0")) ++
                    (for (lhs <- inEqs.iterator) yield ("" + lhs + " >= 0"))
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
