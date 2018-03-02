/**
 * This file is part of ePrincess, a theorem prover based on 
 * Bounded Rigid E-Unification (http://user.it.uu.se/~petba168/breu/) 
 * incoporated into the Princess theorem prover
 * <http://www.philipp.ruemmer.org/princess.shtml>
 * 
 * Copyright (C) 2009-2016 Peter Backeman <peter@backeman.se>
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * ePrincess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ePrincess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with ePrincess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.connection;

import ap.terfor.ConstantTerm
import ap.terfor.preds.PredConj
import ap.util.Debug


// A branch is its list of formulas, an optional pair of nodes
// closing the branch and a number describing what steps have been
// tried .The steps are in range
// [0 .. branch.length - 1 .. branch.length - 1 + |Input Clauses*Clause length|].
// I.e., first we try the nodes on the branch, then the input clauses.

// A term in a BREUOrder which is (_, false) is a constant while
// (_, true) is a variable which can take the value of any variable or
// constant earlier in the order.
abstract class Node {
  override def toString = {
    this match {
      case Literal(formula) => formula.toString
      case FunEquation(eq) => eq.toString
      case Equation(lhs, rhs) => lhs + " = " + rhs
      case NegEquation(lhs, rhs) => lhs + " != " + rhs
    }
  }

  def isLiteral = this.isInstanceOf[Literal]
  def isEquation = this.isInstanceOf[Equation]
  def isNegEquation = this.isInstanceOf[NegEquation]
  def isFunEquation = this.isInstanceOf[FunEquation]

  // TODO: Is this the correct way?
  def asLiteral = this.asInstanceOf[Literal]
  def asEquation = this.asInstanceOf[Equation]
  def asNegEquation = this.asInstanceOf[NegEquation]
  def asFunEquation = this.asInstanceOf[FunEquation]

  // TODO: Cleanup
  def structuralUnifiable(that : Node) : Boolean = {
    (this, that) match {
      case (Literal(formula1), Literal(formula2)) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, formula1.isLiteral && formula2.isLiteral)
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        val formula1atom = (formula1.negativeLits ++ formula1.positiveLits).head
        val formula2atom = (formula2.negativeLits ++ formula2.positiveLits).head

        // Two cases, either formula1 and !formula2 or !formula1 and formula2
        if (!((formula1.negativeLits.length == 1 && formula2.positiveLits.length == 1) ||
          (formula2.negativeLits.length == 1 && formula1.positiveLits.length == 1))) {
          false
        } else if (formula1atom.pred != formula2atom.pred) {
          // They have to share predicate symbol
          false
        } else {
          true
        }
      }
      case _ => false
    }
  }
}
 
case class Literal(formula : PredConj) extends Node
case class FunEquation(eq : PredConj) extends Node
case class Equation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node
case class NegEquation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node

