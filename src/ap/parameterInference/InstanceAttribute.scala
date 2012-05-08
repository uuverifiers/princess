/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parameterInference

import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.CollectingVisitor
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs
//import ap.parser.ContextAwareVisitor
//import ap.parser.CollectingVisitor

/*class NumberOfUniversalQuantifiers(instance:IExpression)
	extends CollectingVisitor[Int,Int]
{
  var attributeValue:Int=0
  
  def calculateAttribute()={attributeValue=visit(instance,0)}
  
  override def preVisit(t : IExpression, a : Int) : PreVisitResult =
    if (attributeValue > 0)
      ShortCutResult(attributeValue)
    else
    t match {
    case IQuantified(Quantifier.ALL, _) => {
      attributeValue = attributeValue + 1
      KeepArg
    }
    case _ =>
      KeepArg
  }
  def postVisit
}*/

object ElementaryAttributes {
  def matchesQuantifier(Arg: Quantifier):
  ((IExpression, Context[Unit]) => Boolean) = {
    case (IQuantified(Arg, _), _) => true
    case _ => false
  }

  def semanticallyMatchesQuantifier(Arg: Quantifier):
  ((IExpression, Context[Unit]) => Boolean) = {
    Arg match {
      case Quantifier.ALL => {
        case (IQuantified(Quantifier.EX, _), ctxt) if ctxt.polarity <= 0 => true
        case (IQuantified(Quantifier.ALL, _), ctxt) if ctxt.polarity >= 0 => true
        case _ => false
      }
      case Quantifier.EX => {
        case (IQuantified(Quantifier.ALL, _), ctxt) if ctxt.polarity <= 0 => true
        case (IQuantified(Quantifier.EX, _), ctxt) if ctxt.polarity >= 0 => true
        case _ => false
      }
    }
  }
  
  def isGround(e:IExpression, ctxt: Context[Unit]):Boolean={
    !ctxt.binders.contains(Quantifier.ALL) //If its already converted to NNF
  }

  def isPositive(e:IExpression, ctxt: Context[Unit]):Boolean={
    e match {
      case e:IBoolLit => ctxt.polarity >= 0
      case e:IConstant => ctxt.polarity >= 0
      case e:IIntLit => ctxt.polarity >= 0
      case e:IVariable => ctxt.polarity >= 0
      case _ => false
    }
  }

  def isNegative(e:IExpression, ctxt: Context[Unit]):Boolean={
    e match {
      case e:IBoolLit => ctxt.polarity <= 0
      case e:IConstant => ctxt.polarity <= 0
      case e:IIntLit => ctxt.polarity <= 0
      case e:IVariable => ctxt.polarity <= 0
      case _ => false
    }
  }
}
class ElementaryAttributes(instance: IExpression)
  extends ContextAwareVisitor[Unit, Unit] {

  val attributeNames: Array[String]=
    Array("No. of universal quantifiers",
        "No. of existential quantifiers",
        "No. of function applications",
        "No. of predicates",
        "No. of semantically universal quantifiers",
        "No. of semantically existential quantifiers",
        "No. of constants",
        "No. of subformulae",
        "No. of leaf nodes with positive polarity",
        "No. of leaf nodes with negative polarity",
        "No. of conjunction nodes",
        "No. of disjunction nodes",
        "No. of negation nodes",
        "No. of equalities",
        "No. of inequalities")
        
  val functionArray: Array[(IExpression, Context[Unit]) => Boolean] =
    Array(ElementaryAttributes.matchesQuantifier(Quantifier.ALL),
      ElementaryAttributes.matchesQuantifier(Quantifier.EX),
      { case (_: IAtom, _) => true; case _ => false },
      { case (_:IFunApp,_)=> true; case _ => false },
      ElementaryAttributes.semanticallyMatchesQuantifier(Quantifier.ALL),
      ElementaryAttributes.semanticallyMatchesQuantifier(Quantifier.EX),
      { case (_:IConstant, _) => true; case _ => false},
      { case _ => true},
      ElementaryAttributes.isPositive,
      ElementaryAttributes.isNegative,
      { case (IBinFormula(IBinJunctor.And,_,_),_) => true; case _ =>false},
      { case (IBinFormula(IBinJunctor.Or,_,_),_) => true; case _ =>false},
      { case (INot(_),_) => true; case _ =>false},
      { case (IIntFormula(IIntRelation.EqZero,_),_) => true; case _ =>false},
      { case (IIntFormula(IIntRelation.GeqZero,_),_) => true; case _ =>false}
      )
  val actionArray: Array[Array[Int]=>Int]=Array()
  
  val attributeValues = Array.fill(functionArray.size)(0) //Switch to ARRAY

  def calculateAttribute() = {
    visit(instance, Context(()))
    attributeValues
  }

  def postVisit(Exp: IExpression, ctxt: Context[Unit],
    subres: Seq[Unit]): Unit = {
    for ( i <- 0 to functionArray.size)
      if (functionArray(i)(Exp,ctxt))
        attributeValues(i) += 1
        
  //attributeValues
  }
  
  /*class CNFSizeEstimate(instance: IExpression)
  extends CollectingVisitor[Tuple2[IBinJunctor.Value,IdealInt], IdealInt]{
  
   override def preVisit(t : IExpression, pair : Tuple2[IBinJunctor.Value,IdealInt]) : PreVisitResult ={
    t match {
      case IBinFormula(IBinJunctor.And,_,_) if pair._1!=IBinJunctor.And => UniSubArgs(IBinJunctor.And)
      case IBinFormula(IBinJunctor.Or,_,_) => UniSubArgs(IBinJunctor.Or)
      case _ => KeepArg
    }
   
  def postVisit(Exp: IExpression, lastConn:IBinJunctor.Value,
      subres: Seq[IdealInt]):IdealInt = {
     
    IdealInt.sum(subres)
      
  	}
  }*/
    
    
 }







  /* Example of traversing with interruption once a goal was found
   * override def preVisit(t : IExpression, a : Int) : PreVisitResult =
    if (attributeValue > 0)
      ShortCutResult(attributeValue)
    else
    t match {
    case IQuantified(Quantifier.ALL, _) => {
      attributeValue = attributeValue + 1
      KeepArg
    }
    case _ =>
      KeepArg
  }*/


/*abstract class InstanceAttribute(instance:IExpression) 
	extends CollectingVisitor
{
  var attributeValue=0
  val baseValue
  //def calc(i:IExpression):Int={visit)=}
  
  def calculateAttribute()={attributeValue=visit(instance,baseValue)}

  case class NumberOfUniversalQuantifiers(instance:IExpression) 
  	extends ContextAwareVisitor[IExpression, Int]
  	{
  
    override def calc(i:IExpression)={
      
    }
  }
}*/