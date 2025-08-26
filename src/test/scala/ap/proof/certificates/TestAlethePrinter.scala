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

val predicates2 = """\functions {
	int a;
}

\predicates {
	p(int);
}

\problem {
	\forall int x; (p(x) -> p(x+1))
->
	p(13)
->
	p(17)
}"""

val predicates2Cert = """; Assumptions after simplification:
; ---------------------------------

(assume input_0 (and (p 13) (not (p 17)) (forall (($v0 Int)) (or (not (p $v0))
        (p (+ $v0 1))))))

; Those formulas are unsatisfiable:
; ---------------------------------

; Begin of proof

(step t1 (cl (not (p 17))) :rule and :premises (input_0) :args (1))
(step t2 (cl (p 13)) :rule and :premises (input_0) :args (0))
(step t3 (cl (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1))))) :rule and
  :premises (input_0) :args (2))

(step t4 (cl (or (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1)))))
      (or (not (p 13)) (p 14)))) :rule forall_inst :args (13))
(step t5 (cl (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1))))) (or
      (not (p 13)) (p 14))) :rule or :premises (t4))
(step t6 (cl (or (not (p 13)) (p 14))) :rule resolution :premises (t3 t5))
(step t7 (cl (not (p 13)) (p 14)) :rule or :premises (t6))
(step t8 (cl (p 14)) :rule resolution :premises (t2 t7))

(step t9 (cl (or (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1)))))
      (or (not (p 14)) (p 15)))) :rule forall_inst :args (14))
(step t10 (cl (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1))))) (or
      (not (p 14)) (p 15))) :rule or :premises (t9))
(step t11 (cl (or (not (p 14)) (p 15))) :rule resolution :premises (t3 t10))
(step t12 (cl (not (p 14)) (p 15)) :rule or :premises (t11))
(step t13 (cl (p 15)) :rule resolution :premises (t8 t12))

(step t14 (cl (or (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1)))))
      (or (not (p 15)) (p 16)))) :rule forall_inst :args (15))
(step t15 (cl (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1))))) (or
      (not (p 15)) (p 16))) :rule or :premises (t14))
(step t16 (cl (or (not (p 15)) (p 16))) :rule resolution :premises (t3 t15))
(step t17 (cl (not (p 15)) (p 16)) :rule or :premises (t16))
(step t18 (cl (p 16)) :rule resolution :premises (t13 t17))

(step t19 (cl (or (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1)))))
      (or (not (p 16)) (p 17)))) :rule forall_inst :args (16))
(step t20 (cl (not (forall (($v0 Int))  (or (not (p $v0)) (p (+ $v0 1))))) (or
      (not (p 16)) (p 17))) :rule or :premises (t19))
(step t21 (cl (or (not (p 16)) (p 17))) :rule resolution :premises (t3 t20))
(step t22 (cl (not (p 16)) (p 17)) :rule or :premises (t21))
(step t23 (cl ) :rule resolution :premises (t1 t18 t22))

; End of proof
"""

val predicates4 = """\predicates {
  p; q; r;  
}

\problem {
  (p() -> q()) & ( !p() -> r())
<->
  (p() & q()) | (!p() & r())
}
"""

val predicates4Cert = """; Assumptions after simplification:
; ---------------------------------

(assume input_0 (or (and (or (not r) p) (or (not q) (not p)) (or (not p) q) (or
        r p)) (and (or (and r (not p)) (and q p)) (or (and p (not q)) (and (not
            r) (not p))))))
(step t1 (cl (and (or (not r) p) (or (not q) (not p)) (or (not p) q) (or r p))
    (and (or (and r (not p)) (and q p)) (or (and p (not q)) (and (not r) (not
            p))))) :rule or :premises (input_0))

; Those formulas are unsatisfiable:
; ---------------------------------

; Begin of proof

; BETA: splitting t1 gives:
(anchor :step t2)
  
  (assume t3 (and (or (not r) p) (or (not q) (not p)) (or (not p) q) (or r p)))
  
  (step t4 (cl (or r p)) :rule and :premises (t3) :args (3))
  (step t5 (cl r p) :rule or :premises (t4))
  (step t6 (cl (or (not p) q)) :rule and :premises (t3) :args (2))
  (step t7 (cl (not p) q) :rule or :premises (t6))
  (step t8 (cl (or (not q) (not p))) :rule and :premises (t3) :args (1))
  (step t9 (cl (not q) (not p)) :rule or :premises (t8))
  (step t10 (cl (or (not r) p)) :rule and :premises (t3) :args (0))
  (step t11 (cl (not r) p) :rule or :premises (t10))
  
  ; BETA: splitting t5 gives:
  (anchor :step t12)
    
    (assume t13 r)
    (step t14 (cl p) :rule resolution :premises (t11 t13))
    
    ; BETA: splitting t9 gives:
    (anchor :step t15)
      
      (assume t16 (not q))
      (step t17 (cl q) :rule resolution :premises (t7 t14))
      
      (step t18 (cl ) :rule resolution :premises (t16 t17))
      
    (step t15 (cl (not (not q))) :rule subproof)
    
    ; splitting t9, second case:
    (step t19 (cl (not p)) :rule resolution :premises (t9 t15))
    
    (step t20 (cl ) :rule resolution :premises (t19 t14))
    
  (step t12 (cl (not r)) :rule subproof)
  
  ; splitting t5, second case:
  (step t21 (cl p) :rule resolution :premises (t5 t12))
  
  ; BETA: splitting t9 gives:
  (anchor :step t22)
    
    (assume t23 (not q))
    (step t24 (cl q) :rule resolution :premises (t7 t21))
    
    (step t25 (cl ) :rule resolution :premises (t23 t24))
    
  (step t22 (cl (not (not q))) :rule subproof)
  
  ; splitting t9, second case:
  (step t26 (cl (not p)) :rule resolution :premises (t9 t22))
  
  (step t27 (cl ) :rule resolution :premises (t26 t21))
  
(step t2 (cl (not (and (or (not r) p) (or (not q) (not p)) (or (not p) q) (or r
          p)))) :rule subproof)

; splitting t1, second case:
(step t28 (cl (and (or (and r (not p)) (and q p)) (or (and p (not q)) (and (not
            r) (not p))))) :rule resolution :premises (t1 t2))

(step t29 (cl (or (and p (not q)) (and (not r) (not p)))) :rule and :premises
  (t28) :args (1))
(step t30 (cl (and p (not q)) (and (not r) (not p))) :rule or :premises (t29))
(step t31 (cl (or (and r (not p)) (and q p))) :rule and :premises (t28) :args
  (0))
(step t32 (cl (and r (not p)) (and q p)) :rule or :premises (t31))

; BETA: splitting t30 gives:
(anchor :step t33)
  
  (assume t34 (and p (not q)))
  
  (step t35 (cl (not q)) :rule and :premises (t34) :args (1))
  (step t36 (cl p) :rule and :premises (t34) :args (0))
  
  ; BETA: splitting t32 gives:
  (anchor :step t37)
    
    (assume t38 (and r (not p)))
    
    (step t39 (cl (not p)) :rule and :premises (t38) :args (1))
    
    (step t40 (cl ) :rule resolution :premises (t39 t36))
    
  (step t37 (cl (not (and r (not p)))) :rule subproof)
  
  ; splitting t32, second case:
  (step t41 (cl (and q p)) :rule resolution :premises (t32 t37))
  
  (step t42 (cl q) :rule and :premises (t41) :args (0))
  
  (step t43 (cl ) :rule resolution :premises (t35 t42))
  
(step t33 (cl (not (and p (not q)))) :rule subproof)

; splitting t30, second case:
(step t44 (cl (and (not r) (not p))) :rule resolution :premises (t30 t33))

(step t45 (cl (not p)) :rule and :premises (t44) :args (1))
(step t46 (cl (not r)) :rule and :premises (t44) :args (0))

; BETA: splitting t32 gives:
(anchor :step t47)
  
  (assume t48 (and r (not p)))
  
  (step t49 (cl r) :rule and :premises (t48) :args (0))
  
  (step t50 (cl ) :rule resolution :premises (t46 t49))
  
(step t47 (cl (not (and r (not p)))) :rule subproof)

; splitting t32, second case:
(step t51 (cl (and q p)) :rule resolution :premises (t32 t47))

(step t52 (cl p) :rule and :premises (t51) :args (1))

(step t53 (cl ) :rule resolution :premises (t45 t52))

; End of proof
"""

val disj = """\functions {

  int x, y;

}

\problem {

  (x = 1 & y = 1 | x = 2 & y = 2)
&
  (x + y = 1 | x + y = -1)

->

  false

}"""

val disjCert = """; Assumptions after simplification:
; ---------------------------------

(assume input_0 (and (or (= 0 (+ y x (- 1))) (= 0 (+ y x 1))) (or (and (= 0 (+ y
            (- 2))) (= 0 (+ x (- 2)))) (and (= 0 (+ y (- 1))) (= 0 (+ x (-
              1)))))))

; Those formulas are unsatisfiable:
; ---------------------------------

; Begin of proof

(step t1 (cl (or (and (= 0 (+ y (- 2))) (= 0 (+ x (- 2)))) (and (= 0 (+ y (-
              1))) (= 0 (+ x (- 1)))))) :rule and :premises (input_0) :args (1))
(step t2 (cl (and (= 0 (+ y (- 2))) (= 0 (+ x (- 2)))) (and (= 0 (+ y (- 1))) (=
        0 (+ x (- 1))))) :rule or :premises (t1))
(step t3 (cl (or (= 0 (+ y x (- 1))) (= 0 (+ y x 1)))) :rule and :premises
  (input_0) :args (0))
(step t4 (cl (= 0 (+ y x (- 1))) (= 0 (+ y x 1))) :rule or :premises (t3))

; BETA: splitting t2 gives:
(anchor :step t5)
  
  (assume t6 (and (= 0 (+ y (- 2))) (= 0 (+ x (- 2)))))
  
  (step t7 (cl (= 0 (+ x (- 2)))) :rule and :premises (t6) :args (1))
  (step t8 (cl (= 0 (+ y (- 2)))) :rule and :premises (t6) :args (0))
  
  ; BETA: splitting t4 gives:
  (anchor :step t9)
    
    (assume t10 (= 0 (+ y x (- 1))))
    
    (step t11 (cl (= 0 (+ x 1)) (not (= 0 (+ y x (- 1)))) (not (= 0 (+ y (-
                2))))) :rule la_generic :args ((- 1) 1 (- 1)))
    (step t12 (cl (= 0 (+ x 1))) :rule resolution :premises (t10 t8 t11))
    
    (step t13 (cl (= 0 3) (not (= 0 (+ x 1))) (not (= 0 (+ x (- 2))))) :rule
      la_generic :args ((- 1) 1 (- 1)))
    (step t14 (cl (= 0 3)) :rule resolution :premises (t12 t7 t13))
    
    (step t15 (cl (= (= 0 3) false)) :rule eq_simplify)
    (step t16 (cl (not (= (= 0 3) false)) (not (= 0 3)) false) :rule equiv_pos2)
    (step t17 (cl (not false)) :rule false)
    (step t18 (cl ) :rule resolution :premises (t14 t15 t16 t17))
    
  (step t9 (cl (not (= 0 (+ y x (- 1))))) :rule subproof)
  
  ; splitting t4, second case:
  (step t19 (cl (= 0 (+ y x 1))) :rule resolution :premises (t4 t9))
  
  (step t20 (cl (= 0 (+ x 3)) (not (= 0 (+ y x 1))) (not (= 0 (+ y (- 2)))))
    :rule la_generic :args ((- 1) 1 (- 1)))
  (step t21 (cl (= 0 (+ x 3))) :rule resolution :premises (t19 t8 t20))
  
  (step t22 (cl (= 0 5) (not (= 0 (+ x 3))) (not (= 0 (+ x (- 2))))) :rule
    la_generic :args ((- 1) 1 (- 1)))
  (step t23 (cl (= 0 5)) :rule resolution :premises (t21 t7 t22))
  
  (step t24 (cl (= (= 0 5) false)) :rule eq_simplify)
  (step t25 (cl (not (= (= 0 5) false)) (not (= 0 5)) false) :rule equiv_pos2)
  (step t26 (cl (not false)) :rule false)
  (step t27 (cl ) :rule resolution :premises (t23 t24 t25 t26))
  
(step t5 (cl (not (and (= 0 (+ y (- 2))) (= 0 (+ x (- 2)))))) :rule subproof)

; splitting t2, second case:
(step t28 (cl (and (= 0 (+ y (- 1))) (= 0 (+ x (- 1))))) :rule resolution
  :premises (t2 t5))

(step t29 (cl (= 0 (+ x (- 1)))) :rule and :premises (t28) :args (1))
(step t30 (cl (= 0 (+ y (- 1)))) :rule and :premises (t28) :args (0))

; BETA: splitting t4 gives:
(anchor :step t31)
  
  (assume t32 (= 0 (+ y x (- 1))))
  
  (step t33 (cl (= 0 x) (not (= 0 (+ y x (- 1)))) (not (= 0 (+ y (- 1))))) :rule
    la_generic :args ((- 1) 1 (- 1)))
  (step t34 (cl (= 0 x)) :rule resolution :premises (t30 t32 t33))
  
  (step t35 (cl (= 0 1) (not (= 0 x)) (not (= 0 (+ x (- 1))))) :rule la_generic
    :args ((- 1) 1 (- 1)))
  (step t36 (cl (= 0 1)) :rule resolution :premises (t29 t34 t35))
  
  (step t37 (cl (= (= 0 1) false)) :rule eq_simplify)
  (step t38 (cl (not (= (= 0 1) false)) (not (= 0 1)) false) :rule equiv_pos2)
  (step t39 (cl (not false)) :rule false)
  (step t40 (cl ) :rule resolution :premises (t36 t37 t38 t39))
  
(step t31 (cl (not (= 0 (+ y x (- 1))))) :rule subproof)

; splitting t4, second case:
(step t41 (cl (= 0 (+ y x 1))) :rule resolution :premises (t4 t31))

(step t42 (cl (= 0 (+ x 2)) (not (= 0 (+ y x 1))) (not (= 0 (+ y (- 1))))) :rule
  la_generic :args ((- 1) 1 (- 1)))
(step t43 (cl (= 0 (+ x 2))) :rule resolution :premises (t30 t41 t42))

(step t44 (cl (= 0 3) (not (= 0 (+ x 2))) (not (= 0 (+ x (- 1))))) :rule
  la_generic :args ((- 1) 1 (- 1)))
(step t45 (cl (= 0 3)) :rule resolution :premises (t29 t43 t44))

(step t46 (cl (= (= 0 3) false)) :rule eq_simplify)
(step t47 (cl (not (= (= 0 3) false)) (not (= 0 3)) false) :rule equiv_pos2)
(step t48 (cl (not false)) :rule false)
(step t49 (cl ) :rule resolution :premises (t45 t46 t47 t48))

; End of proof
"""
}

class TestAlethePrinter extends Properties("TestAlethePrinter") {

  import TestAlethePrinter._

  def checkProof(input : String, cert : String) : Boolean =
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      setConstructProofs(true)

      val (f, _, _) = extractPriInput(input)
      ?? (f)

//      ???
//      println(aletheCertificateAsString())

      ??? == ProverStatus.Valid &&
      aletheCertificateAsString() == cert
    }

  property("inequalities5") =
    checkProof(inequalities5, inequalities5Cert)

  property("predicates2") =
    checkProof(predicates2, predicates2Cert)

  property("predicate4") =
    checkProof(predicates4, predicates4Cert)

  property("disj") =
    checkProof(disj, disjCert)

}
