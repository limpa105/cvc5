; COMMAND-LINE: --decision=justification
; COMMAND-LINE: --sub-cbqi
; EXPECT: unsat

(set-logic AUFLIA)
(set-info :source | 
  Boogie/Spec# benchmarks.
  This benchmark was translated by Michal Moskal.
|)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun InRange (Int Int) Bool)
(declare-fun o () Int)
(declare-fun q () Int)
(declare-fun int_18446744073709551615 () Int)
(declare-fun Smt.false () Int)
(declare-fun anyEqual (Int Int) Int)
(declare-fun y () Int)
(declare-fun select1 (Int Int) Int)
(declare-fun select2 (Int Int Int) Int)
(declare-fun CONCVARSYM (Int) Int)
(declare-fun divides (Int Int) Int)
(declare-fun intAtMost (Int Int) Int)
(declare-fun subtypes (Int Int) Bool)
(declare-fun store1 (Int Int Int) Int)
(declare-fun store2 (Int Int Int Int) Int)
(declare-fun B_0 () Int)
(declare-fun B_1 () Int)
(declare-fun intAtLeast (Int Int) Int)
(declare-fun int_2147483647 () Int)
(declare-fun boolOr (Int Int) Int)
(declare-fun ReallyLastGeneratedExit_correct () Int)
(declare-fun int_m9223372036854775808 () Int)
(declare-fun Smt.true () Int)
(declare-fun int_4294967295 () Int)
(declare-fun start_correct () Int)
(declare-fun B () Int)
(declare-fun F () Int)
(declare-fun G () Int)
(declare-fun boolAnd (Int Int) Int)
(declare-fun boolNot (Int) Int)
(declare-fun k_0 () Int)
(declare-fun intLess (Int Int) Int)
(declare-fun intGreater (Int Int) Int)
(declare-fun anyNeq (Int Int) Int)
(declare-fun is (Int Int) Int)
(declare-fun int_m2147483648 () Int)
(declare-fun modulo (Int Int) Int)
(declare-fun boolImplies (Int Int) Int)
(declare-fun boolIff (Int Int) Int)
(declare-fun int_9223372036854775807 () Int)
(assert true)
(assert true)
(assert (forall ((?A Int) (?i Int) (?v Int)) (= (select1 (store1 ?A ?i ?v) ?i) ?v)))
(assert (forall ((?A Int) (?i Int) (?j Int) (?v Int)) (=> (not (= ?i ?j)) (= (select1 (store1 ?A ?i ?v) ?j) (select1 ?A ?j)))))
(assert (forall ((?A Int) (?o Int) (?f Int) (?v Int)) (= (select2 (store2 ?A ?o ?f ?v) ?o ?f) ?v)))
(assert (forall ((?A Int) (?o Int) (?f Int) (?p Int) (?g Int) (?v Int)) (=> (not (= ?o ?p)) (= (select2 (store2 ?A ?o ?f ?v) ?p ?g) (select2 ?A ?p ?g)))))
(assert (forall ((?A Int) (?o Int) (?f Int) (?p Int) (?g Int) (?v Int)) (=> (not (= ?f ?g)) (= (select2 (store2 ?A ?o ?f ?v) ?p ?g) (select2 ?A ?p ?g)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolIff ?x ?y) Smt.true) (= (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolImplies ?x ?y) Smt.true) (=> (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolAnd ?x ?y) Smt.true) (and (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int) (?y Int)) (= (= (boolOr ?x ?y) Smt.true) (or (= ?x Smt.true) (= ?y Smt.true)))))
(assert (forall ((?x Int)) (! (= (= (boolNot ?x) Smt.true) (not (= ?x Smt.true))) :pattern ((boolNot ?x)) )))
(assert (forall ((?x Int) (?y Int)) (= (= (anyEqual ?x ?y) Smt.true) (= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (! (= (= (anyNeq ?x ?y) Smt.true) (not (= ?x ?y))) :pattern ((anyNeq ?x ?y)) )))
(assert (forall ((?x Int) (?y Int)) (= (= (intLess ?x ?y) Smt.true) (< ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intAtMost ?x ?y) Smt.true) (<= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intAtLeast ?x ?y) Smt.true) (>= ?x ?y))))
(assert (forall ((?x Int) (?y Int)) (= (= (intGreater ?x ?y) Smt.true) (> ?x ?y))))
(assert (distinct Smt.false Smt.true))
(assert (forall ((?t Int)) (! (subtypes ?t ?t) :pattern ((subtypes ?t ?t)) )))
(assert (forall ((?t Int) (?u Int) (?v Int)) (! (=> (and (subtypes ?t ?u) (subtypes ?u ?v)) (subtypes ?t ?v)) :pattern ((subtypes ?t ?u) (subtypes ?u ?v)) )))
(assert (forall ((?t Int) (?u Int)) (! (=> (and (subtypes ?t ?u) (subtypes ?u ?t)) (= ?t ?u)) :pattern ((subtypes ?t ?u) (subtypes ?u ?t)) )))
(assert (let ((?v_0 (forall ((?p Int) (?f Int)) (or (= (select2 B_1 ?p ?f) (select2 B ?p ?f)) (and (= ?p o) (= ?f F))))) (?v_1 (= ReallyLastGeneratedExit_correct Smt.true)) (?v_2 (= start_correct Smt.true))) (not (=> (=> (=> true (=> (= k_0 (select2 B q G)) (=> (= B_0 (store2 B o F (+ y (select2 B o F)))) (=> (= B_1 (store2 B_0 q G k_0)) (=> (=> (=> true (and ?v_0 (=> ?v_0 (=> true true)))) ?v_1) ?v_1))))) ?v_2) ?v_2))))
(check-sat)
(exit)
