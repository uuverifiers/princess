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

import ap.parser.Simplifier
import ap.AbstractFileProver
import ap.basetypes.IdealInt
import ap.basetypes.IdealInt._
import ap.parser._
import ap.parser.CollectingVisitor
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.util.Seqs
import ap.parameters.GlobalSettings
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

  def matchesQuantifier(Arg: Quantifier): ((IExpression, Context[Unit]) => Boolean) = {
    case (IQuantified(Arg, _), _) => true
    case _ => false
  }

  //def calculateAttributes(problems: Seq[(String, () => java.io.Reader)]): Array[Array[Double]] = {
  def calculateAttributes(filename: String, reader : () => java.io.Reader): Array[Double] = {  
  /*if (problems.isEmpty) {
      Console.withOut(Console.err) {
        println("No inputs given, exiting")
      }
      return null
    }*/

    //Debug.enableAllAssertions(Param.ASSERTIONS(settings))
    var res= Array(0.0)
    try {
      //var i=0
      //for ((filename, reader) <- problems)
      try {
        val timeBefore = System.currentTimeMillis

        var lastFilename = (filename split "/").last stripSuffix ".p"
        //print(lastFilename)
        val parser = TPTPTParser.apply(false)
        val r = reader()
        val (f, interpolantSpecs, preSignature) = parser.apply(r)
        r.close
        val timeMid = System.currentTimeMillis
        //System.err.println("Removing equivalences")
        //val neq=EquivExpander.apply(f)
        //System.err.println("Transforming to NNF")
        val nnf = Transform2NNF(f)

        val attributes = new ElementaryAttributes(nnf)
        attributes.calculateAttributes
        val cnfSize = new CNFSizeEstimate(nnf)
        val (clsNum, litNum, _, _) = cnfSize.calculate
        val ground=new GroundAttributes(nnf)
        ground.calculate
        res=attributes.calculateExtendedAttributes(clsNum,litNum,ground.numGroundF,ground.numGroundSubF)
        
        /*for (i <- 0 until attributes.attributeValues.size)
          print(", " + attributes.attributeValues(i))*/

        
        /*print(", " + clsNum)
        print(", " + litNum)
        print(", " + ground.numGroundF)
        print(", " + ground.numGroundSubF)
        println("")*/
        //val timeAfter = System.currentTimeMillis
        //print(","+(timeMid-timeBefore)+","+(timeAfter-timeMid)+"\n")
      }
      res
    }
  }
  def main(args: Array[String]): Unit = {
    import ap.CmdlMain._
    val (settings, inputs) =
      try { // switch on proof construction by default in the iPrincess version
        GlobalSettings.fromArguments(args, GlobalSettings.DEFAULT)
      } catch {
        case e: Throwable => {
          Console.withOut(Console.err) {
            printGreeting
            println
            println(e.getMessage)
            println
            printUsage
          }
          return
        }
      }

    /*if (Param.LOGO(settings)) Console.withOut(Console.err) {
      printGreeting
      println
    }*/
    val a = new ElementaryAttributes(null)
    //for (attr <- a.attributeNames)
      //print(attr + ", ")
      //println("")
    for (name <- inputs.view){
    	val instance=calculateAttributes(name,
    			() => new java.io.BufferedReader(
    			new java.io.FileReader(
    			new java.io.File(name))))
    
    print( ((name split "/").last stripSuffix ".p") + ", ")
    for (i <- 0 until a.attributeNames.size)
    //for (inst <- instance)
    {
    	println(i+": "+instance(i))
    }
    println()
    	/*val cls= new MyClassifier()
    	for ( res <- cls.classify(instance))
    		println(res._1+": "+res._2)*/
    }
  }

  def semanticallyMatchesQuantifier(Arg: Quantifier): ((IExpression, Context[Unit]) => Boolean) = {
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

  //def isGround(e:IExpression, ctxt: Context[Unit]):Boolean=
  //{ case (_:INamedPart,_)|(_:ITerm,_) => false; case (_,ctxt) =>  !ctxt.binders.contains(Quantifier.ALL) //If its already converted to NNF}

  def isPositive(e: IExpression, ctxt: Context[Unit]): Boolean = {
    e match {
      case IExpression.LeafFormula(e) => ctxt.polarity >= 0
      case _ => false
    }
  }

  def isNegative(e: IExpression, ctxt: Context[Unit]): Boolean = {
    e match {
      case IExpression.LeafFormula(e) => ctxt.polarity <= 0
      case _ => false
    }
  }
}

class ElementaryAttributes(instance: IExpression)
  extends ContextAwareVisitor[Unit, Unit] {

  val attributeNames: Array[String] =
    Array("No. of predicates",
      "No. of function applications",
      "No. of universal quantifiers",
      "No. of existential quantifiers",
      "No. of semantically universal quantifiers",
      "No. of semantically existential quantifiers",
      "No. of constants",
      "No. of subformulae",
      "Formula size",
      "No. of leaf nodes with positive polarity",
      "No. of leaf nodes with negative polarity",
      "No. of conjunction nodes",
      "No. of disjunction nodes",
      "No. of negation nodes",
      "No. of equivalence nodes",
      "No. of equalities",
      "No. of inequalities",
      "No. of ground terms",
      "No. of closed subformulae",
      "No. of subterms",
      "No. of Quantifiers",
      "Quants/FormSize",
      "FormSize/Quants",
      "AllQuants/Quants",
      "Quants/AllQuants",
      "ExQuants/Quants",
      "Quants/ExQuants",
      "AllQuants/FormSize",
      "FormSize/AllQuants",
      "ExQuants/FormSize",
      "FormSize/ExQuants",
      "Pred/FormSize",
      "FormSize/Pred",
      "Fun/FormSize",
      "FormSize/Fun",
      //"Are there unused function symbols?",
      "Const/FormSize",
      "FormSize/Const",
      "Leaves",
      "PosLeavesRatio",
      "NegLeavesRatio",
      "OrderedPolarityLeafRatio",
      "Const/Leaves",
      "Leaves/Const",
      "No. of logical connectives (LConn)",
      "And/LConn",
      "Or/LConn",
      "Not/LConn",
      "Eqv/LConn",
      "LConn/And",
      "LConn/Or",
      "LConn/Not",
      "LConn/Eqv",
      "LConn Entropy",
      "LConn mean",
      "LConn standard deviation",
      "LConn/FormSize",
      "FormSize/LConn",
      "Or/CNFLit",
      "Or/CNFCls",
      "And/CNFLit",
      "And/CNFCls",
      "CNFLit/FormSize",
      "FormSize/CNFLit",
      "Eq/FormSize",
      "FormSize/Eq",
      "Ineq/FormSize",
      "FormSize/Ineq",
      "Closed/FormSize",
      "FormSize/Closed",
      "No. of subterms",
      "Subterm/FormulaSize",
      "GroundF/FormSize",
      "FormSize/GroundF",
      "GroundSF/FormSize",
      "FormSize/GroundSF",
      "GroundF/GroundSF",
      "GroundSF/GroundF",
      "CNFLit",
      "CNFCls",      
      "No. of ground formulae",
      "No. of ground subformulae"
      )

  val functionArray: Array[(IExpression, Context[Unit]) => Boolean] =
    Array(
      { case (_: IAtom, _) => true; case _ => false },
      { case (_: IFunApp, _) => true; case _ => false },
      ElementaryAttributes.matchesQuantifier(Quantifier.ALL),
      ElementaryAttributes.matchesQuantifier(Quantifier.EX),
      ElementaryAttributes.semanticallyMatchesQuantifier(Quantifier.ALL),
      ElementaryAttributes.semanticallyMatchesQuantifier(Quantifier.EX),
      { case (_: IConstant, _) => true; case _ => false },
      { case (_: INamedPart, _) | (_: ITerm, _) => false; case _ => true },
      { case (_: INamedPart, _) => false; case _ => true },
      ElementaryAttributes.isPositive,
      ElementaryAttributes.isNegative,
      { case (IBinFormula(IBinJunctor.And, _, _), _) => true; case _ => false },
      { case (IBinFormula(IBinJunctor.Or, _, _), _) => true; case _ => false },
      { case (INot(_), _) => true; case _ => false },
      { case (IBinFormula(IBinJunctor.Eqv, _, _), _) => true; case _ => false },
      { case (IIntFormula(IIntRelation.EqZero, _), _) => true; case _ => false },
      { case (IIntFormula(IIntRelation.GeqZero, _), _) => true; case _ => false },
      { case (_: INamedPart, _) | (_: ITerm, _) => false; case (_, ctxt) => !ctxt.binders.contains(Context.ALL) },
      { case (_: INamedPart, _) | (_: ITerm, _) => false; case (_, ctxt) => ctxt.binders.size == 0 },
      { case (_: ITerm, _) => true; case _ => false })
  //val actionArray: Array[Array[Int]=>Int]=Array()

  val attributeValues = Array.fill(attributeNames.size)(0.0)

  def calculateAttributes() = {
    visit(instance, Context(()))
    //attributeValues
  }

  def postVisit(Exp: IExpression, ctxt: Context[Unit],
    subres: Seq[Unit]): Unit = {
    for (i <- 0 until functionArray.size)
      if (functionArray(i)(Exp, ctxt))
        attributeValues(i) += 1

    //attributeValues
  }

  def calculateExtendedAttributes(cnfcls: IdealInt, cnflit: IdealInt, numGroundF:Int, numGroundSubf:Int): Array[Double] =
    {
      val startInd = functionArray.size

      attributeValues(attributeValues.size-1)=numGroundSubf
      attributeValues(attributeValues.size-2)=numGroundF
      attributeValues(attributeValues.size-3)=cnfcls.doubleValue
      attributeValues(attributeValues.size-4)=cnflit.doubleValue
      //"No. of Quantifiers"
      attributeValues(startInd) = attributeValues(2) + attributeValues(3)

      //"Leaves",
      attributeValues(startInd + 17) = attributeValues(9) + attributeValues(10)

      //"No. of logical connectives (LConn)",
      attributeValues(startInd + 23) = attributeValues(11) + attributeValues(12) +
        attributeValues(13) + attributeValues(14)

      //"No. of subterms"
      attributeValues(startInd + 48) = attributeValues(8) - attributeValues(7)

      //*/FormSize
      if (attributeValues(7) > 0) {
        //"Quants/FormSize",
        attributeValues(startInd + 1) = attributeValues(startInd) / attributeValues(7)
        //"AllQuants/FormSize",
        attributeValues(startInd + 7) = attributeValues(2) / attributeValues(7)
        //"ExQuants/FormSize",
        attributeValues(startInd + 9) = attributeValues(3) / attributeValues(7)
        //"Pred/FormSize",
        attributeValues(startInd + 11) = attributeValues(0) / attributeValues(7)
        //"Fun/FormSize",
        attributeValues(startInd + 13) = attributeValues(1) / attributeValues(7)
        //"Const/FormSize",
        attributeValues(startInd + 15) = attributeValues(6) / attributeValues(7)
        //"LConn/FormSize",
        attributeValues(startInd + 35) = attributeValues(startInd + 23) / attributeValues(7)
        //"CNFLit/Subform",
        attributeValues(startInd + 41) = IdealIntIsIntegral.toDouble(cnflit) / attributeValues(7)
        //"Eq/Subform",
        attributeValues(startInd + 43) = attributeValues(15) / attributeValues(7)
        //"Ineq/FormSize",
        attributeValues(startInd + 45) = attributeValues(16) / attributeValues(7)
        //"Ground/FormSize",
        attributeValues(startInd + 47) = attributeValues(17) / attributeValues(7)
        //"GroundF/FormSize"
        attributeValues(startInd + 50) = numGroundF/ attributeValues(7)
        //"GroundSF/FormSize",
        attributeValues(startInd + 52) = numGroundSubf/ attributeValues(7)
      };
      
      //TrueFormSize
      if (attributeValues(7)>0){
      //"Avg. term size" TODO
        attributeValues(startInd + 49) = attributeValues(48) / attributeValues(7)
      }
        
      
      
      //*/Quants
      if (attributeValues(startInd) > 0) {
        //"FormSize/Quants",
        attributeValues(startInd + 2) = attributeValues(7) / attributeValues(startInd)
        //"AllQuants/Quants",
        attributeValues(startInd + 3) = attributeValues(2) / attributeValues(startInd)
        //"ExQuants/Quants",
        attributeValues(startInd + 5) = attributeValues(3) / attributeValues(startInd)
      };

      //*/AllQuants
      if (attributeValues(2) > 0) {
        //"Quants/AllQuants",
        attributeValues(startInd + 4) = attributeValues(startInd + 1) / attributeValues(2)
        //"FormSize/AllQuants",
        attributeValues(startInd + 8) = attributeValues(7) / attributeValues(2)
      }

      //*/ExQuants
      if (attributeValues(3) > 0) {
        //"Quants/ExQuants",
        attributeValues(startInd + 6) = attributeValues(startInd) / attributeValues(3)
        //"FormSize/ExQuants",
        attributeValues(startInd + 10) = attributeValues(7) / attributeValues(3)
      }

      //*/Pred
      if (attributeValues(0) > 0) {
        //"FormSize/Pred",
        attributeValues(startInd + 12) = attributeValues(8) / attributeValues(0)
      }

      //*/Fun
      if (attributeValues(1) > 0) {
        //"FormSize/Fun",
        attributeValues(startInd + 14) = attributeValues(8) / attributeValues(1)
      }

      //*Const
      if (attributeValues(6) > 0) {
        //"FormSize/Const",
        attributeValues(startInd + 16) = attributeValues(8) / attributeValues(6)
        //"Leaves/Const",
        attributeValues(startInd + 22) = attributeValues(startInd + 17) / attributeValues(6)
      }

      //*/Leaves
      if (attributeValues(startInd + 17) > 0) {
        //"PosLeavesRatio",
        attributeValues(startInd + 18) = attributeValues(9) / attributeValues(startInd + 17)
        //"NegLeavesRatio",
        attributeValues(startInd + 19) = attributeValues(10) / attributeValues(startInd + 17)
        //"OrderedPolarityLeafRatio",
        attributeValues(startInd + 20) = if (attributeValues(startInd + 18) < attributeValues(startInd + 19))
          attributeValues(startInd + 18)
        else attributeValues(startInd + 19)
        //"Const/Leaves",
        attributeValues(startInd + 21) = attributeValues(6) / attributeValues(startInd + 17)
        
      }

      //*/LConn
      if (attributeValues(startInd + 23) > 0) {
        //"And/LConn",
        attributeValues(startInd + 24) = attributeValues(11) / attributeValues(startInd + 23)
        //"Or/LConn",
        attributeValues(startInd + 25) = attributeValues(12) / attributeValues(startInd + 23)
        //"Not/LConn",
        attributeValues(startInd + 26) = attributeValues(13) / attributeValues(startInd + 23)
        //"Eqv/LConn",
        attributeValues(startInd + 27) = attributeValues(14) / attributeValues(startInd + 23)
        //"LConn Entropy",
        for (i <- 0 until 4)
          attributeValues(startInd + 32) -= attributeValues(startInd + 24 + i) * scala.math.log(attributeValues(startInd + 24 + i))
        //"LConn mean",
        for (i <- 0 until 4)
          attributeValues(startInd + 33) += attributeValues(startInd + 24 + i) / 4
        //"LConn dispersion",
        for (i <- 0 until 4)
          attributeValues(startInd + 34) += attributeValues(startInd + 24 + i) * attributeValues(startInd + 24 + i) / 4
        attributeValues(startInd + 34) -= attributeValues(startInd + 33) * attributeValues(startInd + 33)
        attributeValues(startInd + 34) = scala.math.sqrt(attributeValues(startInd + 34))
        //"FormSize/LConn",
        attributeValues(startInd + 36) = attributeValues(8) / attributeValues(startInd + 23)
      }

      //*/And
      if (attributeValues(11) > 0) {
        //"LConn/And",
        attributeValues(startInd + 28) = attributeValues(startInd + 23) / attributeValues(11)
      }

      //*/Or
      if (attributeValues(12) > 0) {
        //"LConn/Or",
        attributeValues(startInd + 29) = attributeValues(startInd + 23) / attributeValues(12)
      }

      //*/Not
      if (attributeValues(13) > 0) {
        //"LConn/Not",
        attributeValues(startInd + 30) = attributeValues(startInd + 23) / attributeValues(13)
      }

      //*/Eqv
      if (attributeValues(14) > 0) {
        //"LConn/Eqv",
        attributeValues(startInd + 31) = attributeValues(startInd + 23) / attributeValues(14)
      }

      //*CNFLit
      if (cnflit > 0) {
        //"Or/CNFLit",
        attributeValues(startInd + 37) = attributeValues(12) / IdealIntIsIntegral.toDouble(cnflit)
        //"And/CNFLit",
        attributeValues(startInd + 39) = attributeValues(11) / IdealIntIsIntegral.toDouble(cnflit)
        //"Subform/CNFLit",
        attributeValues(startInd + 42) = attributeValues(7) / IdealIntIsIntegral.toDouble(cnflit)
      }

      //*/CNFCls
      if (cnfcls > 0) {
        //"Or/CNFCls",
        attributeValues(startInd + 38) = attributeValues(12) / IdealIntIsIntegral.toDouble(cnfcls)
        //"And/CNFCls",
        attributeValues(startInd + 40) = attributeValues(11) / IdealIntIsIntegral.toDouble(cnfcls)
      }

      if (attributeValues(15) > 0) {
        //"Subform/Eq",
        attributeValues(startInd + 44) = attributeValues(7) / attributeValues(15)
      }

      if (attributeValues(16) > 0) {
        //"FormSize/Ineq",
        attributeValues(startInd + 46) = attributeValues(7) / attributeValues(16)
      }

      if (attributeValues(17) > 0) {
        //"FormSize/Ground")
        attributeValues(startInd + 47) = attributeValues(7) / attributeValues(17)
      }
      
      
      if(numGroundF>0){
      //"FormSize/GroundF",
      attributeValues(startInd + 51) = attributeValues(7) / numGroundF
      // "GroundSF/GroundF",
      attributeValues(startInd + 55) = numGroundSubf / numGroundF
      }
      
      if(numGroundSubf>0){
      //"FormSize/GroundSF",
      attributeValues(startInd + 53) = attributeValues(7) / numGroundSubf
      //"GroundF/GroundSF",
      attributeValues(startInd + 54) = (numGroundF+0.0) / numGroundSubf
      }
     
     attributeValues
    }

}

class GroundAttributes(instance: IExpression)
  extends CollectingVisitor[Unit, Boolean] {

  var numGroundF= 0
  var numGroundSubF = 0

  def calculate() = {
    if (visit(instance, ()) == false) {
      numGroundSubF += 1
      numGroundF += 1
    }
  }

  def postVisit(Exp: IExpression, u: Unit,
    subres: Seq[Boolean]): Boolean = {
    Exp match {
      case _: IVariable => true
      case _ =>
        val fn = subres.count({ x => (x == false) })
        if (fn < subres.size) {
          numGroundF += fn
          numGroundSubF += fn
          true
        } else {
          numGroundSubF += fn
          false
        }
    }
  }
}

class CNFSizeEstimate(instance: IExpression)
  extends CollectingVisitor[Unit, (IdealInt, IdealInt, IdealInt, IdealInt)] {

  /*override def preVisit(t : IExpression, pair : Tuple2[IBinJunctor.Value,IdealInt]) : PreVisitResult ={
    t match {
      case IBinFormula(IBinJunctor.And,_,_) if pair._1!=IBinJunctor.And => UniSubArgs(IBinJunctor.And)
      case IBinFormula(IBinJunctor.Or,_,_) => UniSubArgs(IBinJunctor.Or)
      case _ => KeepArg
    }*/
  def calculate() = {
    visit(instance, ())
  }
  def postVisit(Exp: IExpression, u: Unit,
    subres: Seq[(IdealInt, IdealInt, IdealInt, IdealInt)]): (IdealInt, IdealInt, IdealInt, IdealInt) = {

    if ((Exp match { case _: IAtom => true; case _ => false })
      || (Exp match { case _: IIntFormula => true; case _ => false })
      || (Exp match { case _: IBoolLit => true; case _ => false })
      || (Exp match { case _: ITerm => true; case _ => false }))
      (1, 1, 1, 1)
    else if ((subres.size == 1) || (Exp match {case _:ITrigger => true; case _ => false})) //covers INot, INamedPart, etc.
      subres(subres.size-1)
    else {
      Exp match {
        case IBinFormula(IBinJunctor.And, _, _) => (subres(0)._1 * subres(1)._1, subres(0)._1 * subres(1)._2 + subres(0)._2 * subres(1)._1,
          subres(0)._3 + subres(1)._3, subres(0)._4 + subres(1)._4)
        case IBinFormula(IBinJunctor.Or, _, _) => (subres(0)._1 + subres(1)._1, subres(0)._2 + subres(1)._2,
          subres(0)._3 * subres(1)._3, subres(0)._3 * subres(1)._4 + subres(0)._4 * subres(1)._3)
        case IBinFormula(IBinJunctor.Eqv, _, _) => {
          // A eq B <--->
          // ( not A or B) and (not B or A)
          val naorb = (subres(0)._3 + subres(1)._1, subres(0)._4 + subres(1)._2)
          val aornb = (subres(0)._1 + subres(1)._3, subres(0)._2 + subres(1)._4)
          // not (A eq B) <--->
          // ( A and not B) or (not A and B)	
          val aandnb = (subres(0)._1 * subres(1)._3, subres(0)._1 * subres(1)._4 + subres(0)._2 * subres(1)._3)
          val naandb = (subres(0)._3 * subres(1)._1, subres(0)._3 * subres(1)._2 + subres(0)._4 * subres(1)._1)
          // Return value: first two coords are calculated using AND formula second two using OR formula
          (naorb._1 * aornb._1, naorb._1 * aornb._2 + naorb._2 * aornb._1, aandnb._1 + naandb._1, aandnb._2 + naandb._2)
        }

      }
    }
  }
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