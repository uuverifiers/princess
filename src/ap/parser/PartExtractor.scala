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

package ap.parser

import ap.util.Debug

object PartExtractor {
  
  private val AC = Debug.AC_INPUT_ABSY

  def apply(f : IFormula) : List[INamedPart] = {
    val extractor = new PartExtractor
    if (!extractor.visit(f, Context(true)))
      extractor.addPart(f)
    (for ((name, f) <- extractor.parts.elements) yield INamedPart(name, f)).toList
  }

}

/**
 * Class to turn an <code>IFormula</code> into a list of
 * <code>IFormula</code>, the disjuncts of the given formula. The boolean result
 * returned by the visitor tells whether the current (sub)formula has been added
 * to the <code>parts</code> map.
 */
class PartExtractor extends ContextAwareVisitor[Boolean, Boolean] {

  import IExpression._

  private val parts =
    new scala.collection.mutable.LinkedHashMap[PartName, IFormula]
  
  private def addPart(f : IFormula) : Unit = f match {
    case INamedPart(name, f) =>
      parts += (name -> ((parts get name) match {
        case None => f
        case Some(g) => g | f
      }))
    case f =>
      parts += (PartName.NO_NAME -> ((parts get PartName.NO_NAME) match {
        case None => f
        case Some(g) => g | f
      }))
  }

  override def preVisit(t : IExpression, c : Context[Boolean]) : PreVisitResult =
    t match {
      case IBinFormula(IBinJunctor.Or, _, _) if (c.polarity > 0) =>
        super.preVisit(t, c)
      case IBinFormula(IBinJunctor.And, _, _) if (c.polarity < 0) =>
        super.preVisit(t, c)
      case INot(_) =>
        super.preVisit(t, c)
      case INamedPart(_, _) if (!c.a) =>
        throw new Preprocessing.PreprocessingException(
                            "Named formula part in illegal position: " + t)
      case LeafFormula(_) | _ : ITerm =>
        // do not look into atoms or terms
        ShortCutResult(false)
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
