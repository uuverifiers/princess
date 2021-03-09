/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor.TermOrder
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
  
    assertEquals(DepthCountingVisitor.visit(phi, ()), 1)
    assertEquals(DepthCountingVisitor.visit(psi, ()), 2)
    assertEquals(DepthCountingVisitor.visit(psi & psi, ()), 3)
    assertEquals(DepthCountingVisitor.visit(!psi, ()), 3)
    assertEquals(DepthCountingVisitor.visit(psi | phi, ()), 3)
  }

  def testSubstVisitor = {
    val p = new Predicate("p", 2)
    val c = new ConstantTerm("c")
    val cAsIExpr : ITerm = c
    val d = new ConstantTerm("d")
  
    val phi = p(4, cAsIExpr)
    val psi = ex(p(v(0), d))
    val rho = (v(1) === i(15) + c) & p(c, v(1) * 5)
  
    assert (new SimpleSubstVisitor(cAsIExpr, cAsIExpr).visit(phi, ()) eq phi);
    assertEquals(new SimpleSubstVisitor(c, d).visit(phi, ()), p(4, d));
    assertEquals(new SimpleSubstVisitor(d, c).visit(psi, ()), ex(p(v(0), c)));
    assertEquals(new SimpleSubstVisitor(d, v(0)).visit(psi, ()), ex(p(v(0), v(0))));
    assertEquals(new SimpleSubstVisitor(v(1), c).visit(rho, ()),
                 (c === i(15) + c) & p(c, c*5));
  }
  
  def testInputAbsy2Internal = {
    val c = new ConstantTerm("c")
    val d = new ConstantTerm("d")
    val p = new Predicate("p", 2)

    val to = (TermOrder.EMPTY /: List(c, d))((o, c) => o.extend(c)) extendPred p
    
    InputAbsy2Internal(p(4, c), to)
    InputAbsy2Internal(ex(p(v(0), d)), to)
    InputAbsy2Internal((v(1) === i(15) + c) & p(c, v(1) * 5), to)
  }
}
