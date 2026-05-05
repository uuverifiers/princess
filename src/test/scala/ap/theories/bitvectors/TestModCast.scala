/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Philipp Ruemmer <ph_r@gmx.net>
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

// Unit tests for mod_cast simplification rules

package ap.theories.bitvectors

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.parser._
import ap.util.Debug
import ap.parameters.{Param, GlobalSettings}

import org.scalacheck.Properties
import ap.util.Prop._
import ap.util.ExtraAssertions

class TestModCast extends Properties("TestModCast") {
  import IExpression._
  import ModuloArithmetic._

  property("modcast1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x1 = createConstant("x1")
      val x2 = createConstant("x2")
      
      !! (x1 >= 2 & x1 <= 5)
      !! (x2 === cast2Interval(3, 7, x1))
      // This equation is inconsistent with the mod_cast application
      !! (x2 === 6)
      ??? == ProverStatus.Unsat
    }
  }

  property("modcast2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x1 = createConstant("x1")
      val x2 = createConstant("x2")
      
      !! (x1 >= -1 & x1 <= 5)
      !! (x2 === cast2Interval(0, 4, x1))
      !! (x2 >= 1 & x2 <= 3)
      // with the right bwd-propagation, this equation can be inferred directly
      ?? (x1 === x2)
      ??? == ProverStatus.Valid
    }
  }

  property("xor1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x1 = createConstant("x1", UnsignedBVSort(1))
      val x2 = createConstant("x2", UnsignedBVSort(1))
      
      !! (1 === bvxor(x1, x2))
      ?? (x1 =/= x2)
      ??? == ProverStatus.Valid
    }
  }

  property("xor2") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      Debug enableAllAssertions true

      val x1 = createConstant("x1", UnsignedBVSort(1))
      val x2 = createConstant("x2", UnsignedBVSort(1))
      
      !! (0 === bvxor(x1, x2))
      ?? (x1 === x2)
      ??? == ProverStatus.Valid
    }
  }
  
}