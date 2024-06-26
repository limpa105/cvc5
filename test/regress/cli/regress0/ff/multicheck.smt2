; REQUIRES: cocoa
; EXPECT: sat
; EXPECT: sat
; COMMAND-LINE: --ff-solver split --incremental
; COMMAND-LINE: --ff-solver gb --incremental
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(define-sort F () (_ FiniteField 17))
(declare-fun a () F)
(declare-fun b () F)
(assert (= (ff.mul a a) b))
(assert (= a (as ff1 F)))
(check-sat)
(declare-fun c () F)
(assert (= (ff.mul c c) c))
(assert (= (ff.mul c c) b))
(check-sat)
