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

package ap.proof.certificates

import ap.SimpleAPI
import SimpleAPI.ProverStatus

import org.scalacheck.Properties
import ap.util.Prop._

object TestAlethePrinter {
  val inequalities5 = """\functions {
	int x; int y; int z;
}

\problem {
	y >= 5*x - 1 & y <= 5*x
->
	5*z <= y - 1 & 5*z >= y - 2
->
	false
}
"""

  val inequalities5Cert = """; Assumptions after simplification:
; ---------------------------------

(assume input_0 (and (<= 0 (+ (* (- 5) z) y (- 1))) (<= 0 (+ (* 5 z) (* (- 1) y)
        2)) (<= 0 (+ (* (- 1) y) (* 5 x))) (<= 0 (+ y (* (- 5) x) 1))))

; Those formulas are unsatisfiable:
; ---------------------------------

; Begin of proof

(step t1 (cl (<= 0 (+ y (* (- 5) x) 1))) :rule and :premises (input_0) :args
  (3))
(step t2 (cl (<= 0 (+ (* (- 1) y) (* 5 x)))) :rule and :premises (input_0) :args
  (2))
(step t3 (cl (<= 0 (+ (* 5 z) (* (- 1) y) 2))) :rule and :premises (input_0)
  :args (1))
(step t4 (cl (<= 0 (+ (* (- 5) z) y (- 1)))) :rule and :premises (input_0) :args
  (0))

(step t5 (cl (<= 0 (+ (* 5 z) (* (- 5) x) 3)) (not (<= 0 (+ y (* (- 5) x) 1)))
    (not (<= 0 (+ (* 5 z) (* (- 1) y) 2)))) :rule la_generic :args (1 1 1))
(step t6 (cl (<= 0 (+ (* 5 z) (* (- 5) x) 3))) :rule resolution :premises (t1 t3
    t5))

(step t7 (cl (<= 0 (+ z (* (- 1) x))) (not (<= 0 (+ (* 5 z) (* (- 5) x) 3))))
  :rule la_generic :args (5 1))
(step t8 (cl (<= 0 (+ z (* (- 1) x)))) :rule resolution :premises (t6 t7))

(step t9 (cl (<= 0 (+ (* (- 5) z) (* 5 x) (- 1))) (not (<= 0 (+ (* (- 5) z) y (-
            1)))) (not (<= 0 (+ (* (- 1) y) (* 5 x))))) :rule la_generic :args
  (1 1 1))
(step t10 (cl (<= 0 (+ (* (- 5) z) (* 5 x) (- 1)))) :rule resolution :premises
  (t2 t4 t9))

(step t11 (cl (<= 0 (+ (* (- 1) z) x (- 1))) (not (<= 0 (+ (* (- 5) z) (* 5 x)
          (- 1))))) :rule la_generic :args (5 1))
(step t12 (cl (<= 0 (+ (* (- 1) z) x (- 1)))) :rule resolution :premises (t10
    t11))

(step t13 (cl (<= 0 (- 1)) (not (<= 0 (+ (* (- 1) z) x (- 1)))) (not (<= 0 (+ z
          (* (- 1) x))))) :rule la_generic :args (1 1 1))
(step t14 (cl (<= 0 (- 1))) :rule resolution :premises (t12 t8 t13))

(step t15 (cl (= (<= 0 (- 1)) false)) :rule comp_simplify)
(step t16 (cl (not (= (<= 0 (- 1)) false)) (not (<= 0 (- 1))) false) :rule
  equiv_pos2)
(step t17 (cl (not false)) :rule false)
(step t18 (cl ) :rule resolution :premises (t14 t15 t16 t17))

; End of proof
"""
}

class TestAlethePrinter extends Properties("TestAlethePrinter") {

  import TestAlethePrinter._

  property("inequalities5") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      setConstructProofs(true)

      val (f, _, _) = extractPriInput(inequalities5)
      ?? (f)

      ??? == ProverStatus.Valid &&
      aletheCertificateAsString() == inequalities5Cert
    }
  }

}
