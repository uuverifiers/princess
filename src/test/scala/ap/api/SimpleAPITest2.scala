/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2024 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.TerForConvenience

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class SimpleAPITest2 extends Properties("SimpleAPITest2") with ExtraAssertions {

  val expectedOutput = """
-- Declaration of symbols
Sat

-- Adding some assertions (uses methods from TerForConvenience._)
Sat
Unsat
Sat
"""

  property("SimpleAPITest2") = checkOutput(expectedOutput) {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import TerForConvenience._
  import SimpleAPI.ProverStatus

  def part(str : String) = {
    println
    println("-- " + str)
  }
  
  import p._

  part("Declaration of symbols")

  val c = createConstantRaw("c")
  val d = createConstantRaw("d")
  val r = createRelation("r", 0)
  val s = createRelation("s", 0)
  val v = createRelation("v", 0)

  println(p???) // no assertions, Sat
  
  part("Adding some assertions (uses methods from TerForConvenience._)")
  
  scope {
    implicit val o = order

    addAssertion(r & (c === d + 15))
    addAssertion(d >= 100)
    addAssertion(r ==> s)
    println(???) // still Sat

    p.scope {
      addAssertion(s ==> c <= -100)
      println(p???) // Unsat
    }
  
    println(p???) // Sat again
  }
  
  p.shutDown
  }
}
