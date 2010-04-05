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

import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Quantifier
import ap.terfor.preds.Predicate
import ap.util.{Debug, Logic, APTestCase, PlainRange, Seqs}

class TestInputAbsyVisitor(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testDepthVisitor" => testDepthVisitor
      case "testSubstVisitor" => testSubstVisitor
      case "testInputAbsy2Internal" => testInputAbsy2Internal
    }
  }

  import IExpression._
  
  object DepthCountingVisitor extends CollectingVisitor[Unit, Int] {
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Int]) : Int =
      if (subres.isEmpty)
        0
      else
        Seqs.max(subres) + 1
  }
  
  class SimpleSubstVisitor(oldExpr : IExpression, newExpr : IExpression)
         extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit, subres : Seq[IExpression]) : IExpression =
      if (t == oldExpr)
        newExpr
      else
        t update subres
  }
  
  def testDepthVisitor = {
    val p = new Predicate("p", 2)
    val c = new ConstantTerm("c")
  
    val phi = p(4, c)
    val psi = ex(p(v(0), 13))
  
    assertEquals(DepthCountingVisitor.visit(phi, 0), 1)
    assertEquals(DepthCountingVisitor.visit(psi, 0), 2)
    assertEquals(DepthCountingVisitor.visit(psi & psi, 0), 3)
    assertEquals(DepthCountingVisitor.visit(!psi, 0), 3)
    assertEquals(DepthCountingVisitor.visit(psi | phi, 0), 3)
  }

  def testSubstVisitor = {
    val p = new Predicate("p", 2)
    val c = new ConstantTerm("c")
    val cAsIExpr : ITerm = c
    val d = new ConstantTerm("d")
  
    val phi = p(4, cAsIExpr)
    val psi = ex(p(v(0), d))
    val rho = (v(1) === i(15) + c) & p(c, v(1) * 5)
  
    assert (new SimpleSubstVisitor(cAsIExpr, cAsIExpr).visit(phi, 0) eq phi);
    assertEquals(new SimpleSubstVisitor(c, d).visit(phi, 0), p(4, d));
    assertEquals(new SimpleSubstVisitor(d, c).visit(psi, 0), ex(p(v(0), c)));
    assertEquals(new SimpleSubstVisitor(d, v(0)).visit(psi, 0), ex(p(v(0), v(0))));
    assertEquals(new SimpleSubstVisitor(v(1), c).visit(rho, 0),
                 (c === i(15) + c) & p(c, c*5));
  }
  
  def testInputAbsy2Internal = {
    val c = new ConstantTerm("c")
    val d = new ConstantTerm("d")
    val p = new Predicate("p", 2)

    val to = (TermOrder.EMPTY /: List(c, d))((o, c) => o.extend(c, Set.empty)) extend p
    
    InputAbsy2Internal(p(4, c), to)
    InputAbsy2Internal(ex(p(v(0), d)), to)
    InputAbsy2Internal((v(1) === i(15) + c) & p(c, v(1) * 5), to)
  }
}
