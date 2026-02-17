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

// Unit tests for types and sorts

package ap.api

import ap.parser._
import ap.util.Debug
import SimpleAPI.ProverStatus

import org.scalacheck.Properties
import ap.util.Prop._

/**
 * Check that type constraints in quantified formulas are inserted in such a
 * way that triggers are not destroyed.
 */
class TypeTests2 extends Properties("TypeTests2") {

  property("quantifiers1") = {
    Debug enableAllAssertions true
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      setConstructProofs(true)

      val r = createRelation("r", List(Sort.Integer, Sort.Integer))
      val c = createConstant("c", Sort.Nat)

      val f = all(x => r(c, x) ==> x <= 10)

      setPartitionNumber(1)
      !! (f)
      setPartitionNumber(2)
      !! (r(c, 42))

      ??? == ProverStatus.Unsat
    }
  }

  property("quantifiers2") = {
    Debug enableAllAssertions true
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      setConstructProofs(true)

      val r = createRelation("r", List(Sort.Integer, Sort.Integer))
      val c = createConstant("c", Sort.Nat)
      val c2 = createConstant("c2", Sort.Nat)

      val f = all(x => !r(c, x)) | all(x => !r(c2, x))

      setPartitionNumber(1)
      !! (f)
      setPartitionNumber(2)
      !! (r(c, 42))
      !! (r(c2, 42))

      ??? == ProverStatus.Unsat
    }
  }

}