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

package ap.theories.bitvectors

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser._
import ap.parameters.Param
import ap.util.Debug

import org.scalacheck.Properties

class BVInterpolation extends Properties("BVInterpolation") {

  property("abbrev1") = {
    Debug enableAllAssertions true
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._
      import ModuloArithmetic._

      setConstructProofs(true)

      val x = createConstant("x", UnsignedBVSort(16))

      val f1 = abbrev(bvuge(x, bv(16, 10)) & bvule(x, bv(16, 20)))
      val f2 = abbrev(bvuge(x, bv(16, 100)) & bvule(x, bv(16, 110)))

      setPartitionNumber(1)
      !! (f1)
      !! (f2)
      setPartitionNumber(2)
      !! (true)

      ??? == ProverStatus.Unsat &&
      getInterpolants(List(Set(1), Set(2))) == Seq(IBoolLit(false))
    }
  }

  property("abbrev2") = {
    Debug enableAllAssertions true
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._
      import ModuloArithmetic._

      setConstructProofs(true)

      val x = createConstant("x", UnsignedBVSort(16))
      val y = createConstant("y")

      val f1 = abbrev(y > x)
      val f2 = abbrev(y < 0)

      setPartitionNumber(1)
      !! (f1)
      setPartitionNumber(2)
      !! (f2)

      ??? == ProverStatus.Unsat &&
      getInterpolants(List(Set(1), Set(2))).head.toString == "((-1 + y) >= 0)"
    }
  }

}
