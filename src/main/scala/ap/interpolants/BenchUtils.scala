/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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
