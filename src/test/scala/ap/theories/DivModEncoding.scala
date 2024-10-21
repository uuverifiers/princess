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

package ap.theories

import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties

class DivModEncoding extends Properties("DivModEncoding") {

  import IExpression._
  import GroebnerMultiplication.convert2RichMulTerm

  val c = IConstant(new ConstantTerm("c"))
  val d = IConstant(new ConstantTerm("d"))

  property("eDiv") = {
    (i(12) eDiv i(5)) == i(2) &&
    (i(12) eDiv i(-5)) == i(-2) &&
    (i(-12) eDiv i(5)) == i(-3) &&
    (i(-12) eDiv i(-5)) == i(3) &&
    (c eDiv 5).toString == "EPS (((c + -1 * 5 * _0) >= 0) & (((5 * _0 + -1 * (c + -1 * 5)) + -1) >= 0))" &&
    (c eDiv d).toString == """EPS EX EX EX ((((_0 = c) & (_1 = mul(_3, _2))) & (_2 = d)) & (((_0 + -1 * _1) >= 0) & (((_1 + -1 * (_0 + -1 * \if ((_2 >= 0)) \then (_2) \else (-1 * _2))) + -1) >= 0)))""" &&
    (i(12) eDiv i(0)).toString == "EPS false" &&
    (i(-12) eDivWithSpecialZero i(0)).toString == "intDivZero(-12)" &&
    (c eDiv 2).toString == "EPS ((c = 2 * _0) | (c = (2 * _0 + 1)))"
  }

  property("eMod") = {
    (i(12) eMod i(5)) == i(2) &&
    (i(12) eMod i(-5)) == i(2) &&
    (i(-12) eMod i(5)) == i(3) &&
    (i(-12) eMod i(-5)) == i(3) &&
    (c eMod 5).toString == "EPS (((_0 >= 0) & (((5 + -1 * _0) + -1) >= 0)) & EX (c = (5 * _0 + _1)))" &&
    (c eMod d).toString == """EPS (((_0 >= 0) & (((\if ((d >= 0)) \then (d) \else (-1 * d) + -1 * _0) + -1) >= 0)) & EX (c = (mul(_0, d) + _1)))""" &&
    (i(12) eMod i(0)).toString == "EPS false" &&
    (i(-12) eModWithSpecialZero i(0)).toString == "intModZero(-12)"
  }
}
