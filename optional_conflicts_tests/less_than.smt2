(set-option :produce-models true)
(set-logic QF_LIA)
(set-info :source |Tests out a variety of syntaxes that the rewriter should support
by Matthew Sotoudeh
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (and 
            (or 
                (= x 5)
                (= x 6))
            (or 
                (= y 3)
                (= y 4))
            (or (< x y)
                (> x y))
        )
)
(check-sat)
(get-model)