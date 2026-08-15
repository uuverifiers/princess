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

package ap.theories.bitvectors

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.PresburgerTools
import ap.parser._
import ap.parameters.Param
import ap.util.Debug

import org.scalacheck.Properties

class BVQuantifierElimination extends Properties("BVQuantifierElimination") {

  // Testing quantifier elimination on a formula that was handled incorrectly
  property("qe1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._
      import ModuloArithmetic._

      addTheory(ModuloArithmetic)

      val x4 = createConstant("x4", UnsignedBVSort(11))
      val y4 = createConstant("y4", UnsignedBVSort(11))

      val f = all(v1 =>
        ! (-1*y4 + 2047 >= 0 & y4 >= 0 & -1*x4 + 2047 >= 0 & x4 >= 0 &
        _mod_cast(0, 2047, v1 + 1, y4) &
        _mod_cast(0, 2047, y4 + -51, x4) &
        !ex(v0 =>
           (_mod_cast(0, 2047, x4 + 52, v0) & !
            (-1*v1 + 2047 >= 0 & v1 + -1949 >= 0) &
            ! (-1*v1 + 1023 >= 0 & v1 >= 0 & ! (v0 + -1*v1 + -2 === 0 & v1 + -1022 >= 0))))
          )
        )

      val simpF = PresburgerTools.elimQuantifiersWithPreds(asConjunction(f))

      // The formula and result should hold for x4 = 1898 & y4 = 1949

      scope {
        !! (x4 === 1898 & y4 === 1949)
        addConclusion(f)
        assert(??? == ProverStatus.Valid)
      }

      scope {
        !! (x4 === 1898 & y4 === 1949)
        addConclusion(simpF)
        assert(??? == ProverStatus.Valid)
      }

      true
    }
  }

}