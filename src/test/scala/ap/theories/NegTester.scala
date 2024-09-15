/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.parser._
import ap.SimpleAPI
import ap.util.Debug
import ap.types.Sort

import org.scalacheck.Properties
import ap.util.Prop._

/**
 * Test correct SMT-LIB pretty-printing of ADT testers.
 */
class NegTester extends Properties("NegTester") {

  property("main") = {
  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    import ADT._

    Debug enableAllAssertions true

    val listADT =
      new ADT (List("list"),
               List(("nil",  CtorSignature(List(), ADTSort(0))),
                    ("cons", CtorSignature(List(("head", OtherSort(Sort.Integer)),
                                                ("tail", ADTSort(0))),
                                           ADTSort(0)))))

    val Seq(nil, cons) = listADT.constructors
    val Seq(_, Seq(head, tail)) = listADT.selectors

    val c = createConstant("c", listADT.sorts(0))

    addTheory(listADT)

    assertEquals(smtPP(listADT.hasCtor(c, 0)), "(is-nil c)")
    assertEquals(smtPP(!listADT.hasCtor(c, 0)), "(not (is-nil c))")

    assertEquals(smtPP(asIFormula(asConjunction(listADT.hasCtor(c, 0)))), "(forall ((var0 Int)) (not (and (not (= var0 0)) (or (and (is-nil c) (= 0 var0)) (and (is-cons c) (= 1 var0))))))")
    assertEquals(smtPP(asIFormula(asConjunction(!listADT.hasCtor(c, 0)))), "(not (is-nil c))")

    true
  }
  }
}
