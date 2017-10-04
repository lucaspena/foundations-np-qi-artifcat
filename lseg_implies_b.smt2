; list segment backwards implies list segment forwards
; 2 induction hypotheses needed

(define-sort Set (T) (Array T Bool))

(declare-fun hlseg ((Int) (Int)) (Set Int))
(declare-fun lseg ((Int) (Int)) Bool)
(declare-fun lsegrev ((Int) (Int)) Bool)

(declare-const v Int)
(declare-const v2 Int)
(declare-const a Int)
(declare-const b Int)
(declare-const q Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const d1 Int)
(declare-const d2 Int)

; empty set
(declare-const emp (Set Int))
(assert (= emp ((as const (Set Int)) false)))

(declare-fun next (Int) Int)
(assert (= (next -1) -1))

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

; macro for unfolding hlseg
; note that hlseg with y as nil (-1) corresponds to the heaplet for the list from x
(define-fun unfoldhlseg ((x Int) (y Int)) (Set Int)
  (ite (= x y) emp (union (singleton x) (hlseg (next x) y)))
)

; macro for unfolding lseg (binary)
(define-fun unfoldlseg ((x Int) (y Int)) Bool
  (iff (lseg x y)
       (or
         (and (= x y) (= (hlseg x y) emp))
         (and (and (not (= x y)) (lseg (next x) y)) (not (select (hlseg (next x) y) x)))
       )
  )
)

;; no macro for unfolding lsegrev as the existential quantifier introduces a new constant
;; would need to be unfolded manually

; lsegr -> lseg
(define-fun prop_lsegimpliesb ((x Int) (y Int)) Bool
  (implies (lsegrev x y) (lseg x y))
)

; skolemized induction principle for lsegr -> lseg, with recursive defs
(define-fun indr_lsegimpliesb ((x Int) (y Int)) Bool
  (implies
    (implies
      (or
        (and (= c1 c2) (= (hlseg c1 c2) emp))
        (and (and (and (not (= c1 c2)) (= (next v) c2))
                  (lseg c1 v)
             (not (select (hlseg c1 v) c2))))
      )
      (lseg c1 c2))
    (prop_lsegimpliesb x y)
  )
)

; helper
(define-fun theta ((x Int) (y Int) (t Int)) Bool
  (implies (and (= (next t) y) (and (not (= x y)) (not (select (hlseg x t) y))))
           (lseg x y))
)

; helper for second induction principle
(define-fun prop_derived ((x Int) (y Int) (t Int)) Bool
  (implies (lseg x t) (theta x y t))
)
 
; second induction principle for lsegr -> lseg
(define-fun indr_lsegimpliesb_2 ((x Int) (y Int) (t Int)) Bool
  (implies
    (implies
      (or
        (and (= d1 d2) (= (hlseg d1 d2) emp))
        (and (and (and (not (= d1 d2)) (= (next d1) v2)) (theta v2 q d2))
             (not (select (hlseg v2 d2) d1)))
      )
      (theta d1 q d2))
    (prop_derived x y t)
  )
)

(assert (= (unfoldhlseg v2 q) (hlseg v2 q)))
(assert (= (unfoldhlseg d1 d2) (hlseg d1 d2)))
(assert (= (unfoldhlseg q q) (hlseg q q)))

(assert (unfoldlseg c2 c2))
(assert (unfoldlseg d1 q))
(assert (unfoldlseg v2 q))
(assert (unfoldlseg q q))

; lemma about hlseg needed (see hlseg_lemma.smt2)
(assert (implies (select (hlseg (next v2) q) d1)
                 (select (hlseg (next v2) q) (next d1))))

(echo "no induction principle:")
(push)
(assert (not (prop_lsegimpliesb a b)))
(check-sat)
(pop)

(echo "")
(echo "with only one induction principle (weak):")
(push)
(assert (and (indr_lsegimpliesb a b) (not (prop_lsegimpliesb a b))))
(check-sat)
(pop)

(echo "")
(echo "with derived induction principle as well (weak):")
(push)
(assert (and (indr_lsegimpliesb a b) (not (prop_lsegimpliesb a b))))
(assert (indr_lsegimpliesb_2 c1 c2 v))
(check-sat)
(pop)
