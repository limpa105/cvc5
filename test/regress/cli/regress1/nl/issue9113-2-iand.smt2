(set-logic ANIRA)
(set-info :status sat)
(declare-fun a () (Array Int Int))
(declare-fun b () Int)
(declare-fun c () Int)
(assert (= a (store a 1 ((_ iand 3) b 1))))
(assert (= c (+ b 1)))
(check-sat)