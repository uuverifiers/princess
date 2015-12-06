/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010,2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.certificates

import scala.collection.mutable.ArrayBuffer

import ap.util.Debug

object DotLineariser {
  
  private val AC = Debug.AC_CERTIFICATE_LINEARISER
  
  def apply(cert : Certificate) = (new DotLineariser)(cert)
  
}

/**
 * Class for dumping a certificate in the dot/GraphViz format
 */
class DotLineariser {

  def apply(cert : Certificate) : Unit = {
    println("digraph PrincessCertificate {")
    // first print all assumptions used in the proof
    println("{")
    println("rank=source;")
    val ctxt = (LineariserContext(0, 1, Map()) /: cert.assumedFormulas) {
      case (ctxt, f) => (ctxt formulaName f) _2
    }
    println("}")
    
    dump(cert, ctxt)
    for (s <- arcs)
      println(s)
    println("}")
  }
  
  private def isParenthesised(str : String) : Boolean =
    str.size >= 2 && str.head == '(' && str.last == ')' && {
    var depth = 1
    for (c <- str.substring(1, str.size - 1)) c match {
      case ')' if (depth == 1) => return false
      case ')' => depth = depth - 1
      case '(' => depth = depth + 1
      case _ => // nothing
    }
    true
  }
  
  private def formatFormula(f : CertFormula) : String = {
    var str = f.toString
    while (isParenthesised(str))
      str = str.substring(1, str.size - 1)
      
    var res = str take 30
    str = str drop (30 min str.size)
    while (!str.isEmpty) {
      res = res + "\\n" + (str take 30)
      str = str drop (30 min str.size)
    }
      
    res
  }
  
  private def formulaStyle(formula : CertFormula) = formula match {
    case _ if (formula.isTrue) => "shape=none,style=filled,color=green"
    case _ if (formula.isFalse) => "shape=none,style=filled,color=red"
    case _ : CertCompoundFormula => "shape=box"
    case _ => "shape=none,style=filled,color=lightgray"
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private case class LineariserContext(depth : Int,
                                       ruleAppNum : Int,
                                       formulas : Map[CertFormula, (String, Int)]) {
    def increaseDepth = this.copy(depth = depth + 1)
    
    def increaseRuleAppNum = this.copy(ruleAppNum = ruleAppNum + 1)

    private def createFormulaName(formula : CertFormula) : String = {
      val name = newNodeName
      println(name +
              " [" + formulaStyle(formula) + ",label=\"" +
              formatFormula(formula) + "\"];") 
      name
    }
    
    def formulaName(formula : CertFormula) : (String, LineariserContext) =
      (formulas get formula) match {
        case None => {
          val name = createFormulaName(formula)
          (name, this.copy(formulas = formulas + (formula -> (name, depth))))
        }
        case Some((name, _)) => (name, this)
      }
    
    def freshFormulaName(formula : CertFormula) : (String, LineariserContext) = {
      val name = createFormulaName(formula)
      (formulas get formula) match {
        case None => {
          (name, this.copy(formulas = formulas + (formula -> (name, depth))))
        }
        case Some(_) => (name, this)
      }
    }
    
    def updateFormula(formula : CertFormula) : LineariserContext = {
      val oldName = formulas(formula) _1
      val newName = newNodeName
      println(newName + " [shape=none,label=\"" + formatFormula(formula) + "\"];")
      arcs += (oldName + " -> " + newName + " [style=dotted];")
      this.copy(formulas = formulas + (formula -> (newName, depth)))
    }
    
    def formulaDepth(formula : CertFormula) = formulas(formula) _2
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private var formulaCounter = 0
  
  private def newName(nameBase : String) : String = {
    val i = formulaCounter
    formulaCounter = formulaCounter + 1
    nameBase + i
  }
  
  private def newNodeName : String = newName("node")
  
  private val arcs = new ArrayBuffer[String]
  
  private def printInferenceArcs(from : Set[CertFormula], to : Set[CertFormula],
                                 inf : AnyRef, ctxt : LineariserContext)
                                : LineariserContext =
    if (from.size == 1) (ctxt /: to) {
      case (ctxt, to) => {
        val (fromName, ctxt2) = ctxt formulaName from.head
        val (toName, ctxt3) = ctxt freshFormulaName to
        arcs += (fromName + " -> " + toName + arcAttributes(inf, ctxt.ruleAppNum ) + ";")
        ctxt3
      }
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(DotLineariser.AC, to.size == 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      (ctxt /: from) {
        case (ctxt, from) => {
          val (fromName, ctxt2) = ctxt formulaName from
          val (toName, ctxt3) = ctxt formulaName to.head
          arcs += (fromName + " -> " + toName + arcAttributes(inf, ctxt.ruleAppNum ) + ";")
          ctxt3
        }
      }
    }
  
  private def arcAttributes(inf : AnyRef, ruleAppNum: Int) : String = inf match {
    case _ : SplitEqCertificate |
         _ : OmegaCertificate |
         _ : BetaCertificate |
         _ : StrengthenCertificate => " [label=" + ruleAppNum + ",color=red]"
    case _ : CombineEquationsInference |
         _ : CombineInequalitiesInference |
         _ : DirectStrengthenInference |
         _ : PredUnifyInference |
         _ : ReduceInference |
         _ : ReducePredInference |
         _ : AntiSymmetryInference |
         _ : SimpInference => " [label=" + ruleAppNum + ",color=blue]"
    case _ => " [label=" + ruleAppNum + "]"
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def dump(cert : Certificate,
                   ctxt : LineariserContext) : Unit = cert match {
    case BranchInferenceCertificate(infs, childCert, _) => {
      val newFormulaNames = (ctxt /: infs) {
        case (ctxt, inf) =>
          printInferenceArcs(inf.assumedFormulas, inf.providedFormulas,
                             inf, ctxt).increaseRuleAppNum
      }
      
      dump(childCert, newFormulaNames)
    }
    
    case cert => if (cert.localAssumedFormulas.size == 1) {
      
      val newCtxt =
        if ((ctxt formulaDepth cert.localAssumedFormulas.head) == ctxt.depth)
          ctxt
        else
          // introduce a local copy of the formula to improve readibility
          ctxt updateFormula cert.localAssumedFormulas.head
      
      def dumpPremise(i : Int) : Unit = {
        val newCtxt2 = printInferenceArcs(cert.localAssumedFormulas,
                                          cert.localProvidedFormulas(i),
                                          cert, newCtxt.increaseDepth)
        dump(cert(i), newCtxt2.increaseRuleAppNum)
      }
      
      if (cert.localProvidedFormulas.size == 1)
        dumpPremise(0)
      else
        for (i <- 0 until cert.localProvidedFormulas.size) {
          println("subgraph " + newName("cluster") + "{")
          dumpPremise(i)
          println("color=green")
          println("}")
        }
      
    } else {
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(DotLineariser.AC,
                      cert.localProvidedFormulas.size == 1 &&
                      cert.localProvidedFormulas.head.size == 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      val newCtxt = printInferenceArcs(cert.localAssumedFormulas,
                                       cert.localProvidedFormulas.head,
                                       cert, ctxt)
      
      dump(cert(0), newCtxt.increaseRuleAppNum)
      
    }
  }

}