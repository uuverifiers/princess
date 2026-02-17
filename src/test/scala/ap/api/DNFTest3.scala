/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2026 Philipp Ruemmer <ph_r@gmx.net>
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

// Example of DNF conversion for a formula contain array store
// literals

import ap.parser._
import IExpression._
import ap.theories.ExtArray
import ap.util.Debug

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class DNFTest3 extends Properties("DNFTest3") with ExtraAssertions {

  val expectedOutput = """((P32 != 0 & P7 - 2 >= 100000) | (P7 - 2 < 100000 & P32 = 0)) & (P18 != 0 | P19 = 0) & (P19 != 0 | (P19 = 0 & P33 = 0)) & (P19 != 0 | 0 < P2) & (P19 != 0 | P5 = app0) & (P19 != 0 | (P1 >= 0 & 256 - P1 >= 1 & P27 = 256*P0 + P1 & P26 = P1)) & (P19 != 0 | P28 = P27) & (P19 != 0 | P29 = P2 + P7 - 2) & (P19 != 0 | P31 = P3) & (P19 != 0 | (P23 != 0 & P26 != 10) | (P26 = 10 & P23 = 0)) & (P21 != 0 | (P19 = 0 & P21 = 0)) & (P21 != 0 | 0 < P4) & (P21 != 0 | P24 = app1) & (P21 != 0 | P25 = P4 + P7 - 2) & (P21 != 0 | P6 = P20) & (P21 != 0 | P20 = P24) & (P21 = 0 | (P18 = 0 & P19 = 0)) & (P18 != 0 | P19 != 0 | P23 != 0) & (P18 != 0 | P19 != 0 | P6 = P17) & (P18 != 0 | P19 != 0 | P17 = P22) & (P19 != 0 | P21 != 0 | P23 = 0) & (P19 != 0 | P32 = 0 | P33 != 0) & (P19 != 0 | 0 >= P2 | 0 < P29) & (P21 != 0 | 0 >= P4 | 0 < P25) & store(P30, P29, P28) = app0 & store(P22, P25, 20) = app1
ArrayBuffer((((((((((((((((((((((!(((P7 + -2) + -100000) >= 0) & (P33 = 0)) & !(-1 * P2 >= 0)) & (P5 = app0)) & (P1 >= 0)) & (((256 + -1 * P1) + -1) >= 0)) & (P27 = (256 * P0 + P1))) & (P26 = P1)) & (P28 = P27)) & (P29 = (P2 + (P7 + -2)))) & (P31 = P3)) & !(P26 = 10)) & (P18 = 0)) & (P19 = 0)) & !(P23 = 0)) & (P6 = P17)) & (P17 = P22)) & (P32 = 0)) & !(-1 * P29 >= 0)) & !(P21 = 0)) & (store(P30, P29, P28) = app0)) & (store(P22, P25, 20) = app1)), (((((((((((((((((((((((!(((P7 + -2) + -100000) >= 0) & (P33 = 0)) & !(-1 * P2 >= 0)) & (P5 = app0)) & (P27 = (256 * P0 + P1))) & (P26 = P1)) & (P28 = P27)) & (P29 = (P2 + (P7 + -2)))) & (P31 = P3)) & (P26 = 10)) & (P19 = 0)) & !(-1 * P4 >= 0)) & (P24 = app1)) & (P25 = (P4 + (P7 + -2)))) & (P6 = P20)) & (P20 = P24)) & (P21 = 0)) & !(P18 = 0)) & (P23 = 0)) & (P32 = 0)) & !(-1 * P29 >= 0)) & !(-1 * P25 >= 0)) & (store(P30, P29, P28) = app0)) & (store(P22, P25, 20) = app1)))
"""

  property("main") = checkOutput(expectedOutput) {

Debug enableAllAssertions true

SimpleAPI.withProver(enableAssert = true) { p =>
  import p._

  val ar = ExtArray(List(Sort.Integer), Sort.Integer)

  val app0 = createConstant("app0", ar.sort)
  val app1 = createConstant("app1", ar.sort)
  val P0 = createConstant("P0")
  val P1 = createConstant("P1")
  val P2 = createConstant("P2")
  val P3 = createConstant("P3")
  val P4 = createConstant("P4")
  val P5 = createConstant("P5", ar.sort)
  val P6 = createConstant("P6", ar.sort)
  val P7 = createConstant("P7")
  val P8 = createConstant("P8")
  val P9 = createConstant("P9")
  val P10 = createConstant("P10")
  val P11 = createConstant("P11")
  val P12 = createConstant("P12")
  val P13 = createConstant("P13")
  val P14 = createConstant("P14")
  val P15 = createConstant("P15")
  val P16 = createConstant("P16")
  val P17 = createConstant("P17", ar.sort)
  val P18 = createConstant("P18")
  val P19 = createConstant("P19")
  val P20 = createConstant("P20", ar.sort)
  val P21 = createConstant("P21")
  val P22 = createConstant("P22", ar.sort)
  val P23 = createConstant("P23")
  val P24 = createConstant("P24", ar.sort)
  val P25 = createConstant("P25")
  val P26 = createConstant("P26")
  val P27 = createConstant("P27")
  val P28 = createConstant("P28")
  val P29 = createConstant("P29")
  val P30 = createConstant("P30", ar.sort)
  val P31 = createConstant("P31")
  val P32 = createConstant("P32")
  val P33 = createConstant("P33")


  val g =
  (((((((((((((((((((((((((((!(P32 === 0) & (((P7 + -2) + -100000) >= 0)) | (!(((P7 + -2) + -100000) >= 0) & (P32 === 0))) & (!(P18 === 0) | (P19 === 0))) & (!(P19 === 0) | ((P19 === 0) & (P33 === 0)))) & (!(P19 === 0) | !(-1 * P2 >= 0))) & (!(P19 === 0) | (P5 === app0))) & (!(P19 === 0) | ((((P1 >= 0) & (((256 + -1 * P1) + -1) >= 0)) & (P27 === (256 * P0 + P1))) & (P26 === P1)))) & (!(P19 === 0) | (P28 === P27))) & (!(P19 === 0) | (P29 === (P2 + (P7 + -2))))) & (!(P19 === 0) | (P31 === P3))) & (!(P19 === 0) | ((!(P23 === 0) & !(P26 === 10)) | ((P26 === 10) & (P23 === 0))))) & (!(P21 === 0) | ((P19 === 0) & (P21 === 0)))) & (!(P21 === 0) | !(-1 * P4 >= 0))) & (!(P21 === 0) | (P24 === app1))) & (!(P21 === 0) | (P25 === (P4 + (P7 + -2))))) & (!(P21 === 0) | (P6 === P20))) & (!(P21 === 0) | (P20 === P24))) & ((P21 === 0) | ((P18 === 0) & (P19 === 0)))) & ((!(P18 === 0) | !(P19 === 0)) | !(P23 === 0))) & ((!(P18 === 0) | !(P19 === 0)) | (P6 === P17))) & ((!(P18 === 0) | !(P19 === 0)) | (P17 === P22))) & ((!(P19 === 0) | !(P21 === 0)) | (P23 === 0))) & ((!(P19 === 0) | (P32 === 0)) | !(P33 === 0))) & ((!(P19 === 0) | (-1 * P2 >= 0)) | !(-1 * P29 >= 0))) & ((!(P21 === 0) | (-1 * P4 >= 0)) | !(-1 * P25 >= 0))) & (ar.store(P30, P29, P28) === app0)) & (ar.store(P22, P25, 20) === app1))

  println(pp(g))

  println(DNFConverter.mbDNF(g))

}
}
}
