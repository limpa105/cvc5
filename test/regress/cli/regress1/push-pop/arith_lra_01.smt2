; COMMAND-LINE: --incremental --use-soi
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(assert (or (not (>= (+ (* 17 x1 ) (* 46 x1 ) (* (- 8) x2 ) (* 12 x4 ) (* (- 39) x4 ) (* (- 21) x4 ) (* (- 24) x0 ) (* 31 x3 ) (* (- 31) x2 ) (* 37 x0 ) ) (- 8))) (>= (+ (* (- 2) x3 ) (* (- 22) x1 ) ) (- 42)) ))
(assert (or (not (> (+ (* 49 x0 ) (* 34 x2 ) (* 18 x4 ) ) 45)) (not (= (+ (* 39 x3 ) (* (- 50) x0 ) (* 18 x3 ) (* (- 48) x4 ) (* 26 x3 ) (* 36 x3 ) (* 32 x1 ) ) (- 36))) (> (+ (* (- 41) x3 ) (* (- 22) x1 ) (* 5 x4 ) (* 25 x4 ) (* (- 39) x0 ) (* (- 26) x2 ) (* (- 15) x1 ) (* (- 49) x3 ) ) (- 15)) ))
(assert (or (<= (+ (* (- 17) x2 ) (* (- 20) x3 ) (* (- 15) x0 ) (* (- 23) x2 ) (* 27 x3 ) (* 12 x2 ) (* 48 x2 ) (* (- 29) x2 ) ) (- 25)) (= (+ (* 0 x4 ) (* (- 15) x2 ) (* (- 11) x4 ) (* 23 x0 ) (* (- 10) x2 ) (* (- 30) x0 ) (* (- 26) x4 ) ) (- 48)) (not (< (+ (* (- 43) x2 ) (* (- 44) x3 ) (* (- 43) x4 ) (* (- 11) x4 ) (* (- 21) x0 ) (* 15 x1 ) (* (- 45) x3 ) (* 0 x2 ) (* 21 x2 ) (* (- 45) x1 ) (* 8 x0 ) ) (- 5))) ))
(check-sat)
(push 1)
(assert (not (< (+ (* (- 44) x0 ) (* 45 x3 ) (* 34 x2 ) (* 14 x1 ) (* (- 43) x0 ) (* 19 x0 ) (* 12 x3 ) (* (- 49) x2 ) ) (- 21))) )
(check-sat)
(pop 1)
(assert (or (>= (+ (* 21 x0 ) (* (- 15) x3 ) (* 29 x2 ) (* 35 x3 ) (* 39 x4 ) (* 12 x2 ) ) 13) (not (= (+ (* (- 38) x2 ) (* (- 11) x2 ) ) 26)) (< (+ (* 41 x0 ) (* (- 27) x4 ) (* 20 x0 ) (* (- 29) x4 ) (* (- 30) x3 ) (* (- 30) x3 ) (* 21 x4 ) (* (- 15) x2 ) (* 0 x2 ) (* (- 23) x3 ) (* 43 x2 ) ) (- 18)) ))
(assert (or (not (< (+ (* (- 19) x3 ) (* 25 x2 ) (* (- 47) x2 ) (* 39 x4 ) (* (- 15) x3 ) (* 16 x2 ) ) 5)) (>= (+ (* 46 x1 ) (* 9 x2 ) (* 42 x1 ) (* 48 x3 ) (* 20 x0 ) ) 40) ))
(assert (or (not (= (+ (* (- 40) x2 ) (* 24 x3 ) (* 7 x0 ) (* 40 x1 ) (* 28 x4 ) (* 2 x3 ) (* (- 3) x3 ) (* (- 50) x3 ) (* (- 50) x3 ) (* (- 9) x1 ) (* (- 1) x2 ) ) 41)) (= (+ (* (- 1) x0 ) (* 9 x3 ) ) (- 19)) (not (>= (+ (* 37 x2 ) (* 0 x3 ) (* (- 7) x2 ) (* 36 x4 ) (* 32 x0 ) (* (- 45) x0 ) (* 30 x4 ) (* (- 5) x1 ) ) (- 29))) ))
(assert (= (+ (* (- 44) x3 ) (* (- 48) x1 ) (* 49 x0 ) (* (- 12) x0 ) (* (- 6) x4 ) (* (- 11) x0 ) ) 45) )
(assert (not (>= (+ (* (- 20) x0 ) (* (- 5) x0 ) (* 43 x0 ) (* 33 x0 ) (* 35 x1 ) (* (- 30) x2 ) (* (- 4) x4 ) (* 22 x1 ) ) (- 50))) )
(assert (not (> (+ (* 9 x1 ) (* 3 x2 ) (* 37 x1 ) (* (- 39) x4 ) ) 18)) )
(assert (or (not (< (+ (* (- 23) x3 ) (* (- 10) x4 ) (* (- 17) x0 ) (* 19 x2 ) (* 40 x1 ) (* (- 19) x4 ) (* (- 32) x3 ) ) (- 5))) (not (= (+ (* 33 x2 ) (* (- 7) x2 ) (* 37 x2 ) (* 41 x1 ) (* (- 3) x2 ) (* 14 x1 ) (* 45 x0 ) (* (- 14) x1 ) ) 37)) (< (+ (* 3 x3 ) (* (- 26) x1 ) (* (- 24) x0 ) (* (- 20) x2 ) (* 23 x4 ) (* (- 28) x4 ) (* 42 x3 ) (* (- 19) x2 ) (* (- 26) x1 ) (* (- 40) x2 ) ) (- 27)) ))
(check-sat)
(push 1)
(assert (or (not (= (+ (* (- 24) x4 ) (* 7 x4 ) (* (- 12) x1 ) (* 30 x3 ) (* 26 x3 ) (* (- 45) x2 ) (* (- 3) x1 ) (* (- 7) x2 ) (* (- 14) x0 ) ) 10)) (not (>= (+ (* (- 21) x0 ) (* 31 x3 ) (* (- 16) x3 ) (* 22 x0 ) (* 5 x1 ) (* 31 x0 ) (* 8 x4 ) (* 13 x4 ) ) 40)) (not (>= (+ (* (- 38) x1 ) (* 45 x1 ) (* (- 31) x0 ) (* 18 x3 ) (* 0 x2 ) (* (- 32) x4 ) ) (- 19))) ))
(check-sat)
(pop 1)
(assert (not (= (+ (* 11 x3 ) (* (- 27) x0 ) (* 1 x0 ) ) (- 12))) )
(check-sat)
(push 1)
(assert (or (= (+ (* 46 x3 ) (* (- 41) x4 ) (* (- 33) x4 ) (* 32 x2 ) (* (- 13) x2 ) (* 36 x3 ) (* (- 50) x3 ) (* 41 x2 ) (* 34 x4 ) ) (- 48)) (= (+ (* 17 x4 ) (* (- 43) x2 ) (* (- 2) x4 ) (* (- 38) x4 ) ) (- 8)) ))
(check-sat)
(push 1)
(assert (or (not (< (+ (* (- 15) x2 ) (* (- 15) x3 ) ) 24)) (not (< (+ (* (- 4) x1 ) (* 25 x2 ) (* 13 x4 ) (* 13 x2 ) (* (- 31) x0 ) (* 44 x2 ) (* 6 x3 ) (* (- 40) x3 ) (* (- 31) x1 ) (* (- 35) x4 ) ) 9)) ))
(check-sat)
(push 1)
(assert (or (= (+ (* 6 x1 ) (* 7 x3 ) (* (- 15) x2 ) (* 23 x3 ) (* (- 13) x3 ) (* 30 x4 ) (* (- 39) x2 ) (* 27 x4 ) ) 18) (not (< (+ (* (- 4) x4 ) (* (- 35) x1 ) (* 34 x4 ) (* (- 33) x3 ) (* 18 x2 ) (* 28 x0 ) (* (- 15) x4 ) ) 37)) ))
(assert (or (< (+ (* 43 x3 ) (* 17 x2 ) ) (- 45)) (<= (+ (* 37 x3 ) (* 19 x1 ) (* (- 8) x3 ) (* 49 x1 ) (* (- 14) x3 ) (* (- 30) x2 ) (* 14 x0 ) (* 31 x0 ) (* (- 13) x4 ) (* (- 28) x2 ) ) 8) ))
(assert (<= (+ (* (- 35) x2 ) (* (- 15) x3 ) (* (- 6) x0 ) (* 16 x4 ) (* (- 42) x3 ) (* (- 48) x0 ) (* 40 x2 ) (* 26 x3 ) (* 45 x0 ) (* 10 x0 ) ) 27) )
(assert (or (<= (+ (* 12 x1 ) (* (- 33) x3 ) (* 17 x2 ) (* (- 7) x2 ) (* (- 25) x4 ) (* (- 22) x2 ) (* 2 x1 ) (* (- 46) x3 ) (* (- 2) x1 ) (* (- 5) x4 ) (* 7 x4 ) ) (- 10)) (not (>= (+ (* (- 31) x4 ) (* 25 x4 ) (* (- 33) x4 ) (* 9 x3 ) (* (- 48) x4 ) (* (- 31) x1 ) (* (- 18) x0 ) (* 34 x4 ) (* (- 15) x1 ) ) 39)) (not (<= (+ (* 36 x2 ) (* 24 x0 ) (* (- 17) x3 ) (* (- 38) x1 ) (* 2 x2 ) (* 11 x2 ) (* (- 39) x2 ) (* (- 33) x1 ) (* 15 x1 ) (* (- 1) x0 ) (* (- 33) x4 ) ) 32)) ))
(check-sat)
(push 1)
(assert (or (= (+ (* 44 x3 ) (* (- 19) x3 ) (* 38 x0 ) (* 13 x4 ) (* (- 32) x1 ) ) (- 35)) (>= (+ (* 13 x3 ) (* 21 x4 ) (* 34 x3 ) (* 15 x1 ) (* 5 x3 ) (* (- 43) x3 ) (* 11 x0 ) ) 0) ))
(assert (< (+ (* 14 x2 ) (* 38 x0 ) (* (- 42) x2 ) ) (- 44)) )
(assert (or (not (< (+ (* (- 45) x1 ) (* 32 x3 ) (* 36 x1 ) (* 44 x2 ) (* 42 x3 ) (* (- 7) x2 ) (* 2 x1 ) (* (- 23) x1 ) (* 36 x0 ) (* (- 33) x3 ) ) 0)) (not (> (+ (* (- 34) x1 ) (* (- 49) x4 ) (* 15 x1 ) (* 10 x0 ) (* 10 x0 ) (* (- 39) x2 ) (* (- 9) x1 ) (* (- 11) x1 ) (* 10 x3 ) (* (- 11) x4 ) ) (- 38))) (<= (+ (* 10 x3 ) (* (- 34) x2 ) (* (- 13) x0 ) (* 19 x1 ) (* 20 x3 ) (* 9 x0 ) (* (- 33) x1 ) (* (- 44) x4 ) (* (- 37) x2 ) ) (- 32)) ))
(assert (or (<= (+ (* (- 50) x1 ) (* (- 50) x4 ) (* 48 x0 ) (* (- 5) x0 ) (* 40 x0 ) (* 20 x1 ) (* (- 43) x2 ) (* (- 18) x1 ) ) 28) (not (< (+ (* 13 x1 ) (* (- 41) x2 ) (* (- 8) x3 ) (* 33 x4 ) ) (- 32))) (not (< (+ (* 4 x3 ) (* (- 15) x2 ) (* (- 33) x2 ) (* 12 x1 ) (* (- 8) x2 ) ) 35)) ))
(assert (or (= (+ (* 12 x0 ) (* (- 28) x3 ) (* (- 28) x2 ) (* (- 45) x3 ) (* (- 31) x0 ) (* (- 15) x3 ) (* (- 39) x2 ) (* 28 x2 ) ) 16) (not (<= (+ (* 44 x3 ) (* 28 x0 ) (* 20 x4 ) ) 14)) (<= (+ (* 39 x3 ) (* 23 x2 ) (* 24 x3 ) ) 45) ))
(assert (or (not (<= (+ (* (- 10) x0 ) (* (- 8) x3 ) (* (- 49) x3 ) (* (- 19) x3 ) ) 22)) (= (+ (* 17 x3 ) (* (- 42) x4 ) (* 27 x0 ) (* 35 x0 ) (* 42 x3 ) ) 8) ))
(assert (or (not (>= (+ (* (- 5) x0 ) (* 20 x1 ) (* (- 45) x0 ) (* 5 x4 ) (* (- 43) x1 ) (* (- 20) x1 ) (* (- 34) x2 ) ) (- 11))) (not (<= (+ (* (- 5) x1 ) (* 21 x3 ) (* 16 x2 ) (* (- 10) x0 ) (* 35 x3 ) (* (- 23) x3 ) (* 18 x1 ) (* (- 42) x4 ) ) (- 12))) (not (= (+ (* 21 x4 ) (* (- 47) x1 ) (* 35 x4 ) (* (- 5) x1 ) (* (- 43) x1 ) (* (- 21) x1 ) (* 14 x4 ) (* 37 x0 ) (* 17 x2 ) (* 32 x4 ) (* 27 x2 ) ) (- 40))) ))
(assert (or (not (= (+ (* 14 x1 ) (* (- 38) x4 ) (* (- 48) x2 ) (* (- 9) x2 ) (* (- 11) x3 ) (* (- 9) x2 ) (* 5 x1 ) (* (- 48) x1 ) ) 21)) (not (> (+ (* (- 29) x1 ) (* 45 x1 ) (* 48 x0 ) (* (- 2) x1 ) (* 35 x4 ) ) (- 15))) (not (= (+ (* (- 13) x0 ) (* 14 x1 ) (* (- 31) x0 ) (* 19 x3 ) ) (- 37))) ))
(check-sat)
(push 1)
(assert (or (not (<= (+ (* 0 x4 ) (* (- 13) x1 ) (* (- 33) x3 ) (* 34 x2 ) (* (- 27) x2 ) (* (- 46) x0 ) (* 21 x1 ) ) (- 17))) (<= (+ (* 41 x2 ) (* 23 x1 ) (* (- 1) x0 ) (* 35 x4 ) (* 28 x3 ) ) (- 18)) ))
(assert (or (not (= (+ (* 43 x2 ) (* (- 41) x1 ) (* 30 x3 ) (* (- 50) x3 ) (* (- 9) x0 ) ) (- 27))) (>= (+ (* (- 35) x0 ) (* 22 x0 ) ) 38) (not (> (+ (* 9 x2 ) (* (- 45) x3 ) (* 19 x2 ) (* 49 x0 ) (* (- 37) x2 ) (* (- 27) x3 ) (* (- 27) x4 ) ) (- 46))) ))
(assert (or (> (+ (* (- 4) x1 ) (* 49 x2 ) (* 7 x2 ) ) (- 27)) (not (< (+ (* (- 33) x0 ) (* (- 39) x0 ) (* 9 x4 ) (* (- 33) x0 ) ) 9)) (>= (+ (* 6 x3 ) (* 22 x4 ) (* 4 x1 ) (* (- 34) x0 ) ) (- 46)) ))
(assert (not (>= (+ (* 0 x1 ) (* (- 9) x1 ) (* (- 1) x2 ) (* 4 x1 ) (* (- 13) x0 ) (* (- 10) x4 ) (* (- 25) x4 ) (* (- 14) x3 ) (* (- 49) x1 ) ) 43)) )
(assert (or (<= (+ (* 20 x2 ) (* 42 x3 ) (* (- 4) x2 ) (* (- 44) x3 ) (* (- 45) x1 ) (* 45 x2 ) (* (- 40) x4 ) (* 16 x0 ) (* (- 34) x3 ) (* 4 x1 ) (* 41 x1 ) ) 41) (< (+ (* 19 x4 ) (* (- 50) x0 ) (* (- 28) x4 ) (* (- 20) x0 ) ) 17) ))
(assert (or (< (+ (* 35 x0 ) (* 1 x2 ) ) 46) (not (>= (+ (* 26 x0 ) (* 33 x3 ) (* (- 9) x2 ) (* 10 x2 ) (* 41 x2 ) (* (- 28) x1 ) ) 41)) (not (> (+ (* (- 34) x3 ) (* 1 x3 ) (* (- 19) x1 ) ) (- 23))) ))
(assert (or (not (> (+ (* 25 x0 ) (* 17 x4 ) (* 9 x3 ) ) (- 48))) (not (>= (+ (* (- 20) x2 ) (* 14 x0 ) ) (- 45))) ))
(assert (not (<= (+ (* 2 x3 ) (* (- 24) x3 ) (* (- 40) x1 ) (* 3 x0 ) ) (- 36))) )
(assert (not (= (+ (* (- 30) x4 ) (* 11 x1 ) (* (- 11) x0 ) ) (- 29))) )
(assert (not (= (+ (* 44 x4 ) (* (- 22) x4 ) (* 49 x1 ) (* (- 41) x0 ) (* 18 x2 ) ) 21)) )
(check-sat)
(pop 1)
(assert (not (= (+ (* 38 x3 ) (* 7 x2 ) (* (- 23) x4 ) (* (- 28) x3 ) (* 20 x2 ) (* 39 x3 ) (* 17 x2 ) (* 28 x0 ) (* 11 x2 ) (* 29 x4 ) (* (- 43) x0 ) ) (- 2))) )
(assert (not (>= (+ (* 6 x1 ) (* 29 x3 ) (* 25 x4 ) (* (- 4) x3 ) (* (- 13) x4 ) (* 9 x0 ) (* (- 32) x2 ) (* (- 45) x3 ) (* (- 14) x2 ) (* 34 x3 ) (* (- 37) x2 ) ) 14)) )
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (>= (+ (* (- 50) x2 ) (* 48 x1 ) (* 16 x0 ) (* 31 x4 ) (* (- 33) x3 ) ) (- 10)) (not (< (+ (* (- 25) x3 ) (* (- 47) x4 ) (* (- 24) x1 ) (* 27 x3 ) (* 42 x3 ) ) (- 9))) ))
(check-sat)
(pop 1)
(assert (or (not (> (+ (* 49 x0 ) (* (- 28) x3 ) (* (- 47) x1 ) (* (- 29) x1 ) (* (- 2) x0 ) (* (- 43) x4 ) (* (- 46) x4 ) ) 34)) (> (+ (* (- 22) x2 ) (* 45 x0 ) ) (- 29)) ))
(push 1)
(push 1)
(check-sat)
(push 1)
(check-sat)
(push 1)
(assert (or (<= (+ (* (- 22) x4 ) (* (- 39) x1 ) (* (- 9) x1 ) (* (- 32) x1 ) (* 5 x2 ) (* 7 x3 ) (* (- 13) x3 ) (* 31 x3 ) ) 35) (<= (+ (* 44 x2 ) (* 21 x3 ) (* (- 9) x1 ) ) (- 29)) ))
(assert (or (not (>= (+ (* 22 x1 ) (* (- 1) x2 ) (* (- 47) x0 ) (* 12 x4 ) (* (- 42) x4 ) ) 22)) (not (<= (+ (* 32 x0 ) (* 45 x1 ) (* 40 x4 ) (* 44 x4 ) (* 3 x2 ) (* 33 x2 ) ) (- 17))) ))
(check-sat)
(pop 1)
(assert (or (not (> (+ (* (- 26) x1 ) (* 26 x0 ) ) 48)) (>= (+ (* 35 x3 ) (* (- 43) x2 ) (* 29 x0 ) (* (- 31) x2 ) (* (- 20) x2 ) (* 22 x1 ) ) 49) (>= (+ (* (- 31) x2 ) (* (- 2) x1 ) (* (- 45) x2 ) (* 25 x2 ) (* 29 x4 ) (* (- 23) x1 ) (* (- 1) x0 ) (* 18 x1 ) (* 0 x2 ) (* (- 43) x2 ) (* 24 x2 ) ) (- 23)) ))
(assert (or (<= (+ (* 5 x0 ) (* (- 8) x0 ) (* 18 x4 ) (* (- 12) x3 ) (* (- 18) x3 ) (* (- 48) x3 ) (* (- 34) x1 ) (* (- 2) x1 ) (* (- 50) x3 ) (* (- 45) x3 ) ) (- 48)) (>= (+ (* 41 x0 ) (* 25 x2 ) (* (- 17) x2 ) (* (- 6) x0 ) (* (- 48) x3 ) (* (- 36) x3 ) (* 31 x0 ) (* (- 7) x3 ) ) 15) ))
(check-sat)
