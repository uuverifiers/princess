/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023-2024 Philipp Ruemmer <ph_r@gmx.net>
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

/**
 * Test the ability of the SimpleAPI to stop and restart.
 */
import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class SimpleAPITest13 extends Properties("SimpleAPITest13") with ExtraAssertions {

  property("SimpleAPITest13") = SimpleAPI.withProver(enableAssert = true) { p =>

  ap.util.Debug.enableAllAssertions(true)
  import p._

  setConstructProofs(true)

  import IExpression._
  import SimpleAPI.ProverStatus

  val r = createRelation("r", List(Sort.Integer, Sort.Integer))

  !! (all((x, y) => (r(x, y) ==> (r(x+1, 2*y) | r(x+1, 2*y+1)))))
  !! (r(1, 1))
  !! (all(y => !r(7, y)))

  assert(Set(ProverStatus.Unsat, ProverStatus.Running) contains checkSat(false))

  Thread.sleep(300)

  assert(Set(ProverStatus.Unknown, ProverStatus.Unsat, ProverStatus.Running) contains stop(true))
  backtrackToL0
  assert(Set(ProverStatus.Unsat, ProverStatus.Running) contains checkSat(false))
  assert(??? == ProverStatus.Unsat)
  backtrackToL0

  true
  }
}
