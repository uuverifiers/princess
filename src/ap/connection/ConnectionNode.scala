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
import ap.terfor.preds.{PredConj, Atom}
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
      case PositiveLiteral(atom) => atom.toString
      case NegativeLiteral(atom) => "!" + atom.toString        
      case FunEquation(eq) => eq.toString
      case Equation(lhs, rhs) => lhs + " = " + rhs
      case NegEquation(lhs, rhs) => lhs + " != " + rhs
      case True => "True"
    }
  }

  def isLiteral = this.isInstanceOf[PositiveLiteral] || this.isInstanceOf[NegativeLiteral]
  def isPositiveLiteral = this.isInstanceOf[PositiveLiteral]
  def isNegativeLiteral = this.isInstanceOf[NegativeLiteral]  
  def isEquation = this.isInstanceOf[Equation]
  def isNegEquation = this.isInstanceOf[NegEquation]
  def isFunEquation = this.isInstanceOf[FunEquation]

  // TODO: Is this the correct way?
  def asPositiveLiteral = this.asInstanceOf[PositiveLiteral]
  def asNegativeLiteral = this.asInstanceOf[NegativeLiteral]  
  def asEquation = this.asInstanceOf[Equation]
  def asNegEquation = this.asInstanceOf[NegEquation]
  def asFunEquation = this.asInstanceOf[FunEquation]

  def structuralUnifiable(that : Node) : Boolean = {
    (this, that) match {
      case (PositiveLiteral(atom1), NegativeLiteral(atom2)) => atom1.pred == atom2.pred
      case (NegativeLiteral(atom1), PositiveLiteral(atom2)) => atom1.pred == atom2.pred
      case _ => false
    }
  }
}

object Literal {
  def atom2Terms(a : Atom) : List[ConstantTerm] = {
    (for (e <- a.elements) yield {
      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
      Debug.assertInt(ConnectionProver.AC, e.lcSize == 1)
      Debug.assertInt(ConnectionProver.AC, e.getPair(0)._1 == ap.basetypes.IdealInt.ONE)
      Debug.assertInt(ConnectionProver.AC, e.getTerm(0).isInstanceOf[ConstantTerm])
      //-END-ASSERTION-//////////////////////////////////////////////////////////
      e.getTerm(0).asInstanceOf[ConstantTerm]
    }).toList
  }
}

case class PositiveLiteral(lit : Atom) extends Node {
  def args = Literal.atom2Terms(lit)
}

case class NegativeLiteral(lit : Atom) extends Node {
  def args = Literal.atom2Terms(lit)  
}
case class FunEquation(eq : Atom) extends Node
case class Equation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node
case class NegEquation(lhs : ConstantTerm, rhs : ConstantTerm) extends Node
case object True extends Node

