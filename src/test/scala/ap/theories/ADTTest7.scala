/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser._
import ADT._
import ap.types.Sort
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.Prop._

class ADTTest7 extends Properties("ADTTest7") {

  property("ADTTest7") = {

  Debug enableAllAssertions true

  val (storeSort, store, Seq(x, y, z), Seq(upd_x, upd_y, upd_z)) =
    ADT.createRecordType2("Store",
                          List(("x", Sort.Integer),
                               ("y", Sort.Integer),
                               ("z", Sort.Integer)))

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import IExpression._

    val c = createConstant("c", storeSort)
    val d = createConstant("d", storeSort)

    !! (x(c) > 10)
    !! (y(c) < 100)
    !! (y(c) === z(c))
    !! (d === upd_x(c, 5))

    assert(??? == ProverStatus.Sat)

    scope {
      ?? (x(c) > 10)
      assert(??? == ProverStatus.Valid)
    }

    scope {
      ?? (y(d) < 100)
      assert(??? == ProverStatus.Valid)
    }

    scope {
      ?? (x(d) === 5)
      assert(??? == ProverStatus.Valid)
    }

    scope {
      ?? (x(d) > 10)
      assert(??? == ProverStatus.Invalid)
    }

    scope {
      ?? (y(d) === z(d))
      assert(??? == ProverStatus.Valid)
    }

    true
  }

}
}