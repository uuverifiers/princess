/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2017 Philipp Ruemmer <ph_r@gmx.net>
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

  abstract sealed class DeclaredSym[ConstantType,
                                    VariableType,
                                    PredicateType,
                                    FunctionType]
  case class Constant[CT,VT,PT,FT](c : ConstantTerm, k : SymKind, typ : CT)
             extends DeclaredSym[CT,VT,PT,FT]
  case class Variable[CT,VT,PT,FT](index : Int, typ : VT)
             extends DeclaredSym[CT,VT,PT,FT]
  case class Predicate[CT,VT,PT,FT](pred : ap.terfor.preds.Predicate,
                                    matchStatus : Signature.PredicateMatchStatus.Value,
                                    typ : PT)
             extends DeclaredSym[CT,VT,PT,FT]
  case class Function[CT,VT,PT,FT](fun : IFunction, typ : FT)
             extends DeclaredSym[CT,VT,PT,FT]

  class EnvironmentException(msg : String) extends Exception(msg)

}

class Environment[ConstantType, VariableType, PredicateType, FunctionType, SortType]
      extends Cloneable {

  import Environment._
  
  type DSym = DeclaredSym[ConstantType, VariableType, PredicateType,
                          FunctionType]
  
  /** The declared symbols */
  private val signature =
    new scala.collection.mutable.HashMap[String, DSym]
  
  /** The variables bound at the present point, together with their type */
  private val context =
    new scala.collection.mutable.ArrayBuffer[(String, VariableType)]
  
  /** The declared sorts */
  private val sorts =
    new scala.collection.mutable.HashMap[String, SortType]

  /** A <code>TermOrder</code> containing all declared constants */
  private var orderVar = TermOrder.EMPTY
  
  private val partNames = new scala.collection.mutable.HashMap[String, PartName]
  
  def order = orderVar
  def order_=(newOrder : TermOrder) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Environment.AC,
                    signature.valuesIterator forall {
                      case Constant(c, _, _) =>
                         newOrder.orderedConstants contains c
                      case Predicate(pred, _, _) =>
                        newOrder.orderedPredicates contains pred
                      case _ =>
                        true
                    })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    orderVar = newOrder
  }
  
  override def clone : Environment[ConstantType,
                                   VariableType,
                                   PredicateType,
                                   FunctionType,
                                   SortType] = {
    val res = new Environment[ConstantType, VariableType, PredicateType,
                              FunctionType, SortType]
    
    res.signature ++= this.signature
    res.context ++= this.context
    res.sorts ++= this.sorts
    res.partNames ++= this.partNames
    res.orderVar = this.orderVar
    
    res
  }
  
  def clear : Unit = {
    signature.clear
    context.clear
    sorts.clear
    partNames.clear
    orderVar = TermOrder.EMPTY
  }

  def lookupSym(name : String) : DSym =
    (context lastIndexWhere (_._1 == name)) match {
      case -1 => (signature get name) match {
        case Some(t) =>
          t
        case None =>
          throw new EnvironmentException("Symbol " + name + " not declared")
      }
      case index =>
        Variable(context.size - index - 1, context(index)._2)
    }
  
  def lookupSymPartial(name : String) : Option[DSym] =
    (context lastIndexWhere (_._1 == name)) match {
      case -1 => signature get name
      case index => Some(Variable(context.size - index - 1, context(index)._2))
    }
  
  def isDeclaredSym(name : String) : Boolean =
    (context exists (_._1 == name)) || (signature contains name)
  
  def addConstant(c : ConstantTerm, kind : SymKind, typ : ConstantType) : Unit = {
    addSym(c.name, Constant(c, kind, typ))
    orderVar = kind match {
      case Universal =>
        // universal constants are minimal
        orderVar.extend(c)
      case NullaryFunction =>
        // nullary functions are maximal
        orderVar.extend(c, universalConstants ++ existentialConstants)
      case Existential =>
        // existential constants are small than nullary functions, but bigger
        // than universal constants
        orderVar.extend(c, universalConstants)
    }
  }
 
  def addPredicate(pred : ap.terfor.preds.Predicate,
                   matchStatus : Signature.PredicateMatchStatus.Value,
                   typ : PredicateType) : Unit = {
    addSym(pred.name, Predicate(pred, matchStatus, typ))
    orderVar = orderVar extendPred pred
  }
  
  def addPredicate(pred : ap.terfor.preds.Predicate, typ : PredicateType) : Unit =
    addPredicate(pred, Signature.PredicateMatchStatus.Positive, typ)
  
  def addFunction(fun : IFunction, typ : FunctionType) : Unit =
    addSym(fun.name, Function(fun, typ))
  
  def nullaryFunctions : Set[ConstantTerm] = constants(NullaryFunction)
  def universalConstants : Set[ConstantTerm] = constants(Universal)
  def existentialConstants : Set[ConstantTerm] = constants(Existential)
  def nonNullaryFunctions : Set[IFunction] =
    Set.empty ++ (for (Function(f, _) <- signature.values) yield f)
  
  private def constants(kind : SymKind) : Set[ConstantTerm] =
    Set.empty ++ (for (Constant(c, `kind`, _) <- signature.valuesIterator)
                  yield c)
  
  private def addSym(name : String, t : DSym) : Unit =
    if (signature contains name)
      throw new EnvironmentException("Symbol " + name + " is already declared")
    else
      signature.put(name, t)
  
  def pushVar(name : String, typ : VariableType) : Unit =
    context += ((name, typ))

  def popVar : VariableType =
    if (context isEmpty) {
      throw new EnvironmentException("Trying to pop a non-existing variable")
    } else {
      val res = context.last._2
      context reduceToSize (context.size - 1)
      res
    }

  def existsVar(pred : VariableType => Boolean) =
    context exists { case (_, t) => pred(t) }
  
  def declaredVariableNum = context.size
  
  def addSort(name : String, s : SortType) : Unit =
    if (sorts contains name)
      throw new EnvironmentException("Sort " + name + " is already declared")
    else
      sorts.put(name, s)

  def lookupSort(name : String) : SortType =
    (sorts get name) match {
      case Some(s) =>
        s
      case None =>
        throw new EnvironmentException("Sort " + name + " not declared")
    }

  def lookupSortPartial(name : String) : Option[SortType] = sorts get name

  def lookupPartName(name : String) : PartName =
    partNames.getOrElseUpdate(name, new PartName (name))
  
  def predicateMatchConfig : Signature.PredicateMatchConfig =
    Map.empty ++ (for (Predicate(p, s, _) <- signature.values) yield (p, s))

  def toSignature =
    Signature (universalConstants, existentialConstants,
               nullaryFunctions, predicateMatchConfig, order)

  def symbols : Iterator[DSym] = signature.valuesIterator
}
