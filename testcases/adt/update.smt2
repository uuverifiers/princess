

(declare-datatype IntList ( (nil) (cons (head Int) (tail IntList)) ))

(declare-const t IntList)
(declare-const s IntList)

(assert ((_ is cons) t))
(assert (= s ((_ update-field head) t 42)))

(assert (not (and ((_ is cons) s) (= (tail t) (tail s)) (> (head s) 0))))

(check-sat)

