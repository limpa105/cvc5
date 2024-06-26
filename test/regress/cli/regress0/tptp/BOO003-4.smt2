(set-logic ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)

(declare-fun tptp.add ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X $$unsorted) (Y $$unsorted)) (= (tptp.add X Y) (tptp.add Y X))))
(declare-fun tptp.multiply ($$unsorted $$unsorted) $$unsorted)
(assert (forall ((X $$unsorted) (Y $$unsorted)) (= (tptp.multiply X Y) (tptp.multiply Y X))))
(assert (forall ((X $$unsorted) (Y $$unsorted) (Z $$unsorted)) (= (tptp.add X (tptp.multiply Y Z)) (tptp.multiply (tptp.add X Y) (tptp.add X Z)))))
(assert (forall ((X $$unsorted) (Y $$unsorted) (Z $$unsorted)) (= (tptp.multiply X (tptp.add Y Z)) (tptp.add (tptp.multiply X Y) (tptp.multiply X Z)))))
(declare-fun tptp.additive_identity () $$unsorted)
(assert (forall ((X $$unsorted)) (= (tptp.add X tptp.additive_identity) X)))
(declare-fun tptp.multiplicative_identity () $$unsorted)
(assert (forall ((X $$unsorted)) (= (tptp.multiply X tptp.multiplicative_identity) X)))
(declare-fun tptp.inverse ($$unsorted) $$unsorted)
(assert (forall ((X $$unsorted)) (= (tptp.add X (tptp.inverse X)) tptp.multiplicative_identity)))
(assert (forall ((X $$unsorted)) (= (tptp.multiply X (tptp.inverse X)) tptp.additive_identity)))
(declare-fun tptp.a () $$unsorted)
(assert (not (= (tptp.multiply tptp.a tptp.a) tptp.a)))
(set-info :filename BOO003-4)
(check-sat)
