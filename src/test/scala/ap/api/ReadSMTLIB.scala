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
import SimpleAPI.ProverStatus

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class ReadSMTLIB extends Properties("ReadSMTLIB") with ExtraAssertions {

  val filename1 = "ap/api/testfile.smt2"
  val filename2 = "ap/api/testfile2.smt2"
  val filename3 = "ap/api/testfile3.smt2"

  def toReader(name : String) =
    new java.io.InputStreamReader(
      getClass.getClassLoader.getResourceAsStream(name))

  property("main") = {

    SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

scope {
val x = createConstant("x")
!! (x < 100)

// read a file that includes symbol definitions
val Seq(f) = extractSMTLIBAssertions(toReader(filename1))
assert(pp(f) == "x - y >= 1 & y - 50 >= 1")

!! (f)
assert(??? == ProverStatus.Sat) // sat

!! (x < 50)
assert(??? == ProverStatus.Unsat) // unsat
}

scope {
val x = createConstant("x")
val y = createConstant("y")
!! (x < 100)

// read a file without symbol definitions
val Seq(f) = extractSMTLIBAssertions(toReader(filename2))
assert(pp(f) == "x - y >= 1 & y - 50 >= 1")

!! (f)
assert(??? == ProverStatus.Sat) // sat

!! (x < 50)
assert(??? == ProverStatus.Unsat) // unsat
}

scope {
// read a file that includes symbol definitions and some other commands
// that should be ignored
val Seq(f) = extractSMTLIBAssertions(toReader(filename3))
assert(pp(f) == "x - y >= 1 & y - 50 >= 1")
}}

true
  }

}
