(set-logic QF_NIA)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(define-fun B () Int 104729)

(assert (< x (- B 10)))
(assert (<= 0 x))
(assert (<= 0 y))
(assert (< y (- B 10)))
(assert (< z (+ B 10)))
(assert (<= 0 z))

(assert (= (mod (- x (+ z 10)) B) 0))
(assert (= (mod (- y (+ z 13)) B) 0))

(check-sat)

