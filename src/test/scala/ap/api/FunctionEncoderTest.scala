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

package ap.api

import ap.parser._
import ap.util.Debug

import org.scalacheck.Properties

class FunctionEncoderTest extends Properties("FunctionEncoderTest") {

  property("nullary") = {
    Debug.enableAllAssertions(true)
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      val n = createFunction("n", List(), Sort.Integer)

      val f1 = n() === 42
      assert(asConjunction(f1).toString == "ALL (! (_0 + -42 != 0 & n(_0)))")

      val f2 = (n() >= 1) ==> Sort.Integer.all(x => n() === 2*x)
      assert(asConjunction(f2).toString == "ALL (! (_0 + -1 >= 0 & n(_0)))")

      val f3 = (n() >= 1) ==>
        containFunctionApplications(Sort.Integer.all(x => n() === 0))
      assert(asConjunction(f3).toString == "ALL (! (_0 + -1 >= 0 & n(_0)))")

      // In previous versions, the following formula led to an assertion
      // failure in the FunctionEncoder
      val f4 = Sort.Integer.all(y => (n() >= 1) ==> (
        containFunctionApplications(Sort.Integer.all(x => n() === 0))))
      assert(asConjunction(f4).toString == "ALL (! (_0 + -1 >= 0 & n(_0)))")

      true
    }
  }

}