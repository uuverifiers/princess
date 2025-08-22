/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.bitvectors

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._

// Bit-vector preprocessing
class TestBVPreproc extends Properties("TestBVPreproc") {

  property("bvand/bvadd") = {
    Debug enableAllAssertions true
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._
      import ModuloArithmetic._

      addTheory(ModuloArithmetic)

      val x = createConstant("x", UnsignedBVSort(32))
      val y = createConstant("y", UnsignedBVSort(32))
      val f = bv_and(32, x, bv_add(32, bv(32, 4), bv(32, 10))) === y
      val g = bv_add(32, x, bv_add(32, bv(32, 10), y)) === x

      f.toString ==
        "(bv_and(32, x, bv_add(32, mod_cast(0, 4294967295, 4), mod_cast(0, 4294967295, 10))) = y)" &&
      preprocessIFormula(f).toString ==
        """\part[formula] ALL bv[32]. ALL ALL ALL (!bv_extract(0, 0, _3[bv[32]], _2) | (!bv_extract(3, 1, _3[bv[32]], _1) | (!bv_extract(31, 4, _3[bv[32]], _0) | (ALL ALL (!bv_extract(3, 1, _1, _0) | (((!(_1 = x) | !(_4 = 0)) | !(_3 = _0)) | !(_2 = 0))) | (_3[bv[32]] = y)))))""" &&
      g.toString ==
        "(bv_add(32, x, bv_add(32, mod_cast(0, 4294967295, 10), y)) = x)" &&
      preprocessIFormula(g).toString ==
        """\part[formula] ALL (!mod_cast(0, 4294967295, (x + (10 + y)), _0) | (_0 = x))"""
    }
  }

}