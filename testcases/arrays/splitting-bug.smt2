; Example for which Princess erroneously answered sat

(set-logic AUFLIA)

(assert (exists ( (a (Array Int Int)) (b (Array Int Int)) (c (Array Int Int)) (x Int))
    
      (and (= (store a 1 2) b) 
          (= (store b 1 2) c)
          (or (> x 0) (not (= b c)))
          (or (< x 0) (not (= b c)))
      
    )))

(check-sat)