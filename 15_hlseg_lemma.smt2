(define-sort Set (T) (Array T Bool))

(declare-fun hlseg ((Int) (Int) (Set Int)) Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const d1 Int)
(declare-const d2 Int)

(declare-const H2 (Set Int))
(declare-const H3 (Set Int))
(declare-const H4 (Set Int))
(declare-const H5 (Set Int))
(declare-const Hs (Set Int))
(declare-const Hs2 (Set Int))
(declare-const Hns (Set Int))
(declare-const Hd (Set Int))
(declare-const He (Set Int))

; empty set
(declare-const emp (Set Int))
(assert (= emp ((as const (Set Int)) false)))

(declare-fun next (Int) Int)
(assert (= (next -1) -1))

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

;; no macro for unfolding hlseg as the existential quantifier introduces a new constant
;; needs to be unfolded manually

; prop to prove: if z \in hlseg(x, y), then n(z) \in hlseg(x, y)
(define-fun prop_hlseg ((x Int) (y Int) (z Int) (H (Set Int))) Bool
  (implies (hlseg x y H)
           (implies (select H z) (select H (next z))))
  )

; induction principle for prop_hlseg, recursive definitions
(define-fun indr_hlseg ((x Int) (y Int) (z Int) (H (Set Int))) Bool
  (implies
    (implies
      (or
        (and (= c1 c2) (= Hs emp))
        (and (not (= c1 c2))
             (and (= Hs (union H3 (singleton c1)))
                  (and (hlseg (next c1) c2 H3)
                       (implies (select H3 c3) (select H3 (next c3))))))
      )
      (implies (select Hs c3) (select Hs (next c3))))
    (prop_hlseg x y z H)
  )
)

; equivalent to (unfoldhlseg c1 c2 Hs)
(assert
 (iff (hlseg c1 c2 Hs)
       (or
         (and (= c1 c2) (= Hs emp))
         (and (not (= c1 c2)) (and (= Hs (union H2 (singleton c1))) (hlseg (next c1) c2 H2)))
       )
  )
)

; equivalent to (unfoldhlseg (next c1) c2 H3)
(assert
  (iff (hlseg (next c1) c2 H3)
       (or
         (and (= c1 c2) (= H3 emp))
         (and (not (= c1 c2)) (and (= H3 (union H4 (singleton c1))) (hlseg (next c1) c2 H4)))
       )
  )
)

(echo "no induction principle:")
(push)
(assert (not (prop_hlseg a b c Hd)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_hlseg a b c Hd) (not (prop_hlseg a b c Hd))))
(check-sat)
(pop)
