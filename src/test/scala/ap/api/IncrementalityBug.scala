/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2026 Philipp Ruemmer <ph_r@gmx.net>
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

// case that previously led to an exception, since a
// formula with incompatible term order was added to
// the ModelSearchProver

import ap._
import ap.parser._

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class IncrementalityBug extends Properties("Incrementalitybug") with ExtraAssertions {

  property("main") = {
SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

{


scope {

val A2_0_2 = createConstant("A2_0_2") // addConstantRaw(A2_0_2)
val N = createConstant("N") // addConstantRaw(N)
val __eval0 = createConstant("__eval0") // addConstantRaw(__eval0)

???
//println("59: " + ???)

eval(A2_0_2)
//println("72: " + eval(A2_0_2))

?? ((((__eval0 + 1) + ((N + 1) * -1)) === 0))
checkSat(true)
//println("73: " + checkSat(true)) // checkSat(false)

} // pop scope


}} // withProver
    true
  }
}
