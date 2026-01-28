/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2015-2026 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.parser._

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class Nonlinear extends Properties("Nonlinear") with ExtraAssertions {

  val expectedOutput = """0: Sat
{c1 -> -1, c0 -> -4}
1: Sat
{c1 -> 3, c0 -> 4}
2: Unsat
3: Invalid
{c0 -> -1}
4: Valid
5: Valid
"""

  property("main") = checkOutput(expectedOutput) {

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._
{


reset
}
{
val c0 = createConstant("c0")
val c1 = createConstant("c1")

scope {
!! (c0 ** c1 >= 4)
println("0: " + ???)
println(partialModel)
!! (c0 >= 3)
!! (c1 >= 3)
println("1: " + ???)
println(partialModel)
!! (c0 ** c1 < 7)
println("2: " + ???)
} // pop scope


scope {
?? (((c0 + 1) ^ 2) >= (c0 ^ 2))
println("3: " + ???)
println(partialModel)
!! (c0 >= 0)
println("4: " + ???)
} // pop scope

scope {
?? (c0 ** c1 === c1 ** c0)
println("5: " + ???)
} // pop scope

}}
  }
}
