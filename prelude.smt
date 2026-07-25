(set-logic HO_ALL)
(set-option :produce-unsat-cores true)
(declare-datatype Pair (par (T1 T2) ((pair (fst T1) (snd T2)))))
(declare-datatype Option (par (T) ((some (the T)) (none))))

; ---------------------------------------------------------------------------
; B integer division and modulo.
;
; B truncates towards zero, whereas SMT-LIB's `div`/`mod` are Euclidean, so the
; two disagree on negative operands (B: -7 / 2 = -3, SMT-LIB: (div -7 2) = -4).
; `bdiv` reduces every case to a division of non-negative operands, for which
; the two notions coincide, and `bmod` is derived from it so that
; a = b * (bdiv a b) + (bmod a b) holds by construction.
; ---------------------------------------------------------------------------
(define-fun bdiv ((a Int) (b Int)) Int
  (ite (>= a 0)
    (ite (> b 0) (div a b)          (- (div a (- b))))
    (ite (> b 0) (- (div (- a) b))  (div (- a) (- b)))))
(define-fun bmod ((a Int) (b Int)) Int (- a (* b (bdiv a b))))

; ---------------------------------------------------------------------------
; B integer exponentiation.
;
; SMT-LIB has no exponentiation, so `bpow` is uninterpreted and constrained by
; its defining recursion plus the sign/unit facts solvers need most often.
; The recursion only fires on positive exponents, which keeps instantiation
; well-founded (each unfolding decreases the exponent towards the base case).
; ---------------------------------------------------------------------------
(declare-fun bpow (Int Int) Int)
(assert (forall ((a Int)) (= (bpow a 0) 1)))
(assert (forall ((a Int) (n Int)) (=> (> n 0) (= (bpow a n) (* a (bpow a (- n 1)))))))
(assert (forall ((n Int)) (=> (>= n 0) (= (bpow 1 n) 1))))
(assert (forall ((a Int) (n Int)) (=> (and (>= a 0) (>= n 0)) (>= (bpow a n) 0))))
(assert (forall ((a Int) (n Int)) (=> (and (> a 0) (>= n 0)) (> (bpow a n) 0))))
