; Example in which we previously incorrectly reported unsat; this was
; due to a bug in the factorisation of polynomials

(set-info :status sat)
(declare-fun skoT () Int)
(declare-fun skoB () Int)
(declare-fun skoA () Int)
(declare-fun skoS () Int)

(declare-const var0 Int)
(declare-const var1 Int)
(declare-const var2 Int)
(declare-const var3 Int)
(declare-const var4 Int)
(declare-const var5 Int)
(declare-const var6 Int)
(declare-const var7 Int)
(declare-const var8 Int)
(declare-const var9 Int)

(assert
(and
(not (=
               skoT 0))

(<= 0 (+ var0 (- 1)))

               (= (* skoS skoS) var3)

     (= (* skoA skoA) var1)

     (= (* skoT skoT) var2)

     (= (* var0 var4) var1)       ; var4 = skoA^2

    (= (* var0 var5) var2)       ; var5 = skoT^2

    (= (* skoT (+ var5 var4)) var6)

       (= (* var7 skoT) var8)

    (= (* var0 var7) var6)    ; var7 = skoT * (skoA^2 + skoT^2)

    (= (* var0 var9) var8)

    (= (* var0 var9) var3)))

(check-sat)
