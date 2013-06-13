/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap.basetypes.IdealInt
import ap.parser.IExpression._
import ap.parser.{IFormula, INamedPart, IAtom, IExpression, PartName, IBinJunctor, IInterpolantSpec}
import ap.terfor.ConstantTerm
import ap.parser.CollectingVisitor
import ap.terfor.TerForConvenience._


object PredicateReplace
{
  def apply(f : IExpression, map : Map[IAtom, ConstantTerm]) : IExpression =
  {
    val replacer = new PredicateReplace(map)
    replacer.visit(f, ())
  }
}

class PredicateReplace(map : Map[IAtom, ConstantTerm])
  extends CollectingVisitor[Unit, IExpression]
{
  def postVisit(t : IExpression,
                u : Unit,
                subres : Seq[IExpression]) : IExpression = 
  t match
  {
    case a : IAtom if(a.length == 0) => map(a) === 0
    case _ : IAtom => throw new Error("Prediactes with arity greater that 0 are not supported")
    case _ => t.update(subres)
  }
}

object PredicateCollector {
  def apply(t : IExpression) : scala.collection.Set[IAtom] = {
    val c = new PredicateCollector
    c.visit(t, ())
    c.predicates
  }
}

class PredicateCollector extends CollectingVisitor[Unit, Unit] {
  val predicates = new scala.collection.mutable.HashSet[IAtom]
  
  def postVisit(t : IExpression, u : Unit, subres : Seq[Unit]) : Unit =
    t match {
      case a : IAtom if (a.length==0) =>
        predicates += a
      case _ : IAtom => throw new Error("Prediactes with arity greater than 0 are not supported")  
      case _ => // nothing
    }
}
