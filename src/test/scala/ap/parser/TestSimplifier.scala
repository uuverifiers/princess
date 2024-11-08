/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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

import org.scalacheck.Properties

// Some simple tests for pretty-printing of formulas
class TestSimplifier extends Properties("TestSimplifier") {

  import IExpression._

  property("equations") = {
    val simp = new Simplifier
    val c = new ConstantTerm("c")
    val d = new ConstantTerm("d")

    simp(IEquation(c + 1, d + 2)).toString == "((-1 + (c + -1 * d)) = 0)" &&
    simp(IEquation(c, c*3)).toString == "(c = 0)" &&
    simp(eqZero(c - d)) == IEquation(c, d) &&
    simp(IEquation(5, c)).toString == "(c = 5)" &&
    simp(-c + 5 === 8).toString == "(c = -3)" &&
    simp(c + 5 === 3).toString == "(c = -2)"
  }

  property("inequalities") = {
    val simp = new Simplifier
    val c = new ConstantTerm("c")

    simp(c*2 >= 0).toString == "(c >= 0)" &&
    simp(c*(-2) >= 0).toString == "(-1 * c >= 0)"
  }

  property("inlining-conj") = {
    val simp = new Simplifier
    val c = new ConstantTerm("c")

    // For this formula, we previously got an incorrect rewriting to
    // EX ((c = 2 * _0) & (c = 3 * _0))
    val f = ex(x => ex(y => ex(z1 => c === 2*z1) & ex(z2 => c === 3*z2) & (x === 2*y)))

    simp(f).toString == "(EX ((c + -2 * _0) = 0) & EX ((c + -3 * _0) = 0))"
  }

}