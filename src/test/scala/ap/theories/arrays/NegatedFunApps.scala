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

package ap.theories.arrays

import ap.parser._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import ap.util.Debug

import org.scalacheck.Properties

/**
 * Test that the array theory can correctly handle negated occurrences
 * of function applications, even when constructing proofs.
 */
class NegatedFunApps extends Properties("NegatedFunApps") {
  import IExpression._

  val Array = ExtArray(Seq(Sort.Integer), Sort.Integer)

  property("negRead") = {
    Debug.enableAllAssertions(true)
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import Array.{store, select, sort => ArSort}

      setConstructProofs(true)

      val c = createConstant("c", ArSort)
      val d = createConstant("d", ArSort)

      !! (d === store(c, 1, 2))

      val f = asConjunction(select(d, 1) === 2)
      val _select = f.predicates.iterator.next
      val _d = f.constants.iterator.next
      val a = Atom(_select,
                   List(LinearCombination(_d, order),
                        LinearCombination(1),
                        LinearCombination(2)),
                   order)

      addConclusion(a)

      ??? == ProverStatus.Valid
    }
  }

}
