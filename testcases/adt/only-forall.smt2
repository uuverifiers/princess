
( declare-datatypes ( ( f 0 ) ) ( ( ( g ) ( h ( i Int ) ( j f ) ) ) ) )
( declare-datatypes ( ( d1 0 ) ) ( ( ( b ( c d1 ) ( d111 d1 ) ) ( e ) ) ) )

;( declare-fun p ( f d1 f ) Bool )
(define-fun p ((A f) (B d1) (C f)) Bool (or (or (and (and (= (_size A) (_size C)) (= (_size B) 1)) (>= (_size C) 1)) (and (and (and (is-b B) (= (_size B) 3)) (and (>= (_size A) 1) (>= (_size C) 1))) (is-b B))) (and (and (and (is-b B) (and (and (and (or (and (is-g A) (>= (_size B) 4)) (and (is-h A) (>= (+ (- 1) (_size B)) 4))) (or (and (is-g A) (>= (_size B) 5)) (and (is-h A) (>= (+ 1 (_size B)) 5)))) (>= (_size A) 1)) (>= (_size C) 1))) (is-b B)) (= (mod (+ 1 (_size C)) 2) 0))))

( assert ( forall ( ( s f ) ( w d1 ) ( y d1 ) ( z f ) ) ( => ( and ( p s w s ) ( p z y z ) ) ( p s ( b w y ) z ) ) ) )

(check-sat)
