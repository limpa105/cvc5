(set-option :produce-models true)
(set-logic QF_LIA)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (and 
            (or 
                (= x 20)
                (= x 10))
            (or 
                (= y 30)
                (= y 15)
            )
            (or
                (= x y)
                (= x (+ y 5))
            )
        )
)
(check-sat)
(get-model)