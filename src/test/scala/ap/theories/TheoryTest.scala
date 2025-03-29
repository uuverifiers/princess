/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2025 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.parser._
import ap.SimpleAPI.ProverStatus

import org.scalacheck.Properties
import ap.util.Prop._

class TheoryTest extends Properties("TheoryTest") {

  property("TheoryTest") = {
SimpleAPI.withProver(enableAssert = true) { p =>
  import p._
  import IExpression._

  val ar = SimpleArray(2)
  val a, b, c = createConstant
  implicit val _ = decoderContext

  scope {
    !! (b === ar.store(a, 0, 1, 2))
    !! (c === ar.store(b, 1, 2, 3))

    scope {
      assertEquals(???, ProverStatus.Sat)
      assertEquals(ar.asMap(eval(c)).toList.sortBy(_._2).toString,
                   "List((Vector(0, 1),2), (Vector(1, 2),3))")

      !! (ar.select(c, 0, 2) > 0)
      assertEquals(???, ProverStatus.Sat)
      assertEquals(ar.asMap(eval(c)).toList.sortBy(_._2).toString,
                   "List((Vector(0, 2),1), (Vector(0, 1),2), (Vector(1, 2),3))")

      !! (ar.select(b, 0, 2) < 0)
      assertEquals(???, ProverStatus.Unsat)
    }

    scope {
      ?? (ar.select(c, 0, 1) > 0)
      ??? == ProverStatus.Valid
    }
  }

}
}
}
