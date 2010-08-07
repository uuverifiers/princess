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

package ap.parser;

import ap.Signature
import ap.terfor.{VariableTerm, ConstantTerm, TermOrder}
import ap.util.{FilterIt, Debug}

object Environment {
  
  private val AC = Debug.AC_ENVIRONMENT
  
  abstract sealed class SymKind
  case object NullaryFunction extends SymKind
  case object Universal extends SymKind
  case object Existential extends SymKind

  abstract sealed class DeclaredSym
  case class Constant(c : ConstantTerm, k : SymKind) extends DeclaredSym
  case class Variable(index : Int) extends DeclaredSym
  case class Predicate(pred : ap.terfor.preds.Predicate) extends DeclaredSym
  case class Function(fun : IFunction) extends DeclaredSym

  class EnvironmentException(msg : String) extends Exception(msg)

}

class Environment {

  import Environment._
  
  /** The declared symbols */
  private val signature = new scala.collection.mutable.HashMap[String, DeclaredSym]
  
  /** The variables bound at the present point */
  private val context = new scala.collection.mutable.ArrayBuffer[String]
  
  /** A <code>TermOrder</code> containing all declared constants */
  private var orderVar = TermOrder.EMPTY
  
  private val partNames = new scala.collection.mutable.HashMap[String, PartName]
  
  def order = orderVar
  def order_=(newOrder : TermOrder) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Environment.AC,
                    signature.valuesIterator forall {
                      case Constant(c, _) => newOrder.orderedConstants contains c
                      case Predicate(pred) => newOrder.orderedPredicates contains pred
                      case _ => true
                    })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    orderVar = newOrder
  }
  
  override def clone : Environment = {
    val res = new Environment
    
    res.signature ++= this.signature
    res.context ++= this.context
    res.orderVar = this.orderVar
    
    res
  }
  
  def lookupSym(name : String) : DeclaredSym = (context lastIndexOf name) match {
    case -1 => (signature get name) match {
      case Some(t) => t
      case None => throw new EnvironmentException("Symbol " + name + " not declared")
    }
    case index => Variable(context.size - index - 1)
  }
  
  def addConstant(c : ConstantTerm, kind : SymKind) : Unit = {
    addSym(c.name, Constant(c, kind))
    orderVar = kind match {
      case Universal =>
        // universal constants are minimal
        orderVar.extend(c, Set.empty)
      case NullaryFunction =>
        // nullary functions are maximal
        orderVar.extend(c, universalConstants ++ existentialConstants)
      case Existential =>
        // existential constants are small than nullary functions, but bigger
        // than universal constants
        orderVar.extend(c, universalConstants)
    }
  }
 
  def addPredicate(pred : ap.terfor.preds.Predicate) : Unit = {
    addSym(pred.name, Predicate(pred))
    orderVar = orderVar extend pred
  }
  
  def addFunction(fun : IFunction) : Unit =
    addSym(fun.name, Function(fun))
  
  def nullaryFunctions : Set[ConstantTerm] = constants(NullaryFunction)
  def universalConstants : Set[ConstantTerm] = constants(Universal)
  def existentialConstants : Set[ConstantTerm] = constants(Existential)
  def nonNullaryFunctions : Set[IFunction] =
    Set.empty ++ (for (Function(f) <- signature.values) yield f)
  
  private def constants(kind : SymKind) : Set[ConstantTerm] = {
    val predicate : DeclaredSym => Boolean = {
      case Constant(_, `kind`) => true
      case _ => false
    }
    Set.empty ++ (for (Constant(c, _) <-
                    FilterIt(signature.valuesIterator, predicate))
                  yield c)
  }
  
  private def addSym(name : String, t : DeclaredSym) : Unit =
    if (signature contains name)
      throw new EnvironmentException("Symbol " + name + " is already declared")
    else
      signature += (name -> t)
  
  def pushVar(name : String) : Unit = (context += name)

  def popVar : Unit =
    if (context isEmpty)
      throw new EnvironmentException("Trying to pop a non-existing variable")
    else
      context reduceToSize (context.size - 1)
  
  def lookupPartName(name : String) : PartName =
    partNames.getOrElseUpdate(name, new PartName (name))
  
  def toSignature =
    new Signature (universalConstants, existentialConstants,
                   nullaryFunctions, order)
}
