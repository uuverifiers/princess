/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.util.Debug

object PartExtractor {
  
  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : List[INamedPart] = apply(f, true)

  def apply(f : IFormula, errorForIllegalNames : Boolean) : List[INamedPart] = {
    val extractor = new PartExtractor(errorForIllegalNames)
    if (!extractor.visit(f, Context(true)))
      extractor.addPart(f)
    (for ((name, f) <- extractor.parts.iterator) yield INamedPart(name, f)).toList
  }

  def addPart(toAdd : IFormula, name : PartName,
              otherParts : Seq[INamedPart]) : List[INamedPart] = {
    var selPart : INamedPart = null
    var unchangedParts : List[INamedPart] = List()
        
    for (p @ INamedPart(n, _) <- otherParts)
      if (n == name)
        selPart = p
      else
        unchangedParts = p :: unchangedParts
        
    val newSelPart = selPart match {
      case null             => INamedPart(name, !toAdd)
      case INamedPart(_, f) => INamedPart(name, f | !toAdd)
    }

    newSelPart :: unchangedParts
  }

}

/**
 * Class to turn an <code>IFormula</code> into a list of
 * <code>IFormula</code>, the disjuncts of the given formula. The boolean result
 * returned by the visitor tells whether the current (sub)formula has been added
 * to the <code>parts</code> map.
 */
class PartExtractor private (errorForIllegalNames : Boolean)
      extends ContextAwareVisitor[Boolean, Boolean] {

  import IExpression._

  private val parts =
    new scala.collection.mutable.LinkedHashMap[PartName, IFormula]
  
  private def addPart(f : IFormula) : Unit = f match {
    case INamedPart(name, f) =>
      parts.put(name, ((parts get name) match {
        case None => f
        case Some(g) => g | f
      }))
    case f =>
      parts.put(PartName.NO_NAME, ((parts get PartName.NO_NAME) match {
        case None => f
        case Some(g) => g | f
      }))
  }

  override def preVisit(t : IExpression, c : Context[Boolean]) : PreVisitResult =
    t match {
      case LeafFormula(_) | _ : ITerm =>
        // do not look into atoms or terms
        ShortCutResult(false)
      case IBinFormula(IBinJunctor.Or, _, _) if (c.polarity > 0) =>
        super.preVisit(t, c)
      case IBinFormula(IBinJunctor.And, _, _) if (c.polarity < 0) =>
        super.preVisit(t, c)
      case INot(_) =>
        super.preVisit(t, c)
      case INamedPart(_, _) if (errorForIllegalNames && !c.a) =>
        throw new Preprocessing.PreprocessingException(
                            "Named formula part in illegal position: " + t)
      case _ =>
        // no named parts are allowed underneath other connectives
        super.preVisit(t, if (c.a) c(false) else c)
    }

  def postVisit(t : IExpression, c : Context[Boolean],
                subres : Seq[Boolean]) : Boolean = {
    def add(subExpr : IExpression) = {
      val subFormula = subExpr.asInstanceOf[IFormula]
      addPart(if (c.polarity > 0) subFormula else !subFormula)
    }
    
    t match {
      case IBinFormula(IBinJunctor.Or | IBinJunctor.And, _, _) => subres match {
        case Seq(false, false) => false
        case Seq(true, false) => { add(t(1)); true }
        case Seq(false, true) => { add(t(0)); true }
        case _ => true
      }
      case INot(_) =>
        subres(0)
      case g @ INamedPart(name, f) => {
        addPart(if (c.polarity > 0) g else INamedPart(name, !f))
        true
      }
      case _ => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(PartExtractor.AC, subres forall (false == ))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        false
      }
    }
  }
}

/**
 * Visitor that eliminates all occurrences of the <code>INamedPart</code>
 * operator from a formula.
 */
object PartNameEliminator extends PredPartNameEliminator(_ => true)

/**
 * Visitor that eliminates occurrences of the <code>INamedPart</code>
 * operator from a formula. All parts with a name accepted by
 * <code>toElim</code> will be stripped of their name.
 */
class PredPartNameEliminator(toElim : PartName => Boolean)
      extends CollectingVisitor[Unit, IExpression] {

  def apply(f : IFormula) : IFormula = this.visit(f, ()).asInstanceOf[IFormula]

  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[IExpression]) : IExpression = t match {
    case INamedPart(name, _) if toElim(name) => subres(0)
    case _ => t update subres
  }

}
