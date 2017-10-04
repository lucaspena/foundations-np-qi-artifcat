(define-sort Set (T) (Array T Bool))

(declare-fun list (Int) Bool)
(declare-fun hlseg ((Int) (Int)) (Set Int))
(declare-fun lseg ((Int) (Int)) Bool)

(declare-const a Int)
(declare-const b Int)
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
(define-fun unfoldhlseg ((x Int) (y Int)) (Set Int)
  (ite (= x y) emp (union (singleton x) (hlseg (next x) y)))
)

; macro for unfolding list
(define-fun unfoldlist ((x Int)) Bool
  (iff (list x)
       (or
         (= x -1)
         (and (not (= x -1))
              (and (list (next x)) (not (select (hlseg (next x) -1) x))))
       )
  )
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

; prop to prove: if x->y is an lseg and y is a list, then x is a list
(define-fun prop_lseglist ((x Int) (y Int)) Bool
  (implies (and (list y) (lseg x y)) (list x))
)

; skolemized induction principle, no recursive definitions
(define-fun ind_lseglist ((x Int) (y Int)) Bool
  (implies
    (implies
      (and
        (or
         (= c2 -1)
         (and (not (= c2 -1))
              (and (list (next c2)) (not (select (hlseg (next c2) -1) c2))))
        )
        (or
          (and (= c1 c2) (= (hlseg c1 c2) emp))
          (and (and (not (= c1 c2))
                    (list (next c1)))
               (not (select (hlseg (next c1) c2) c1)))
        ))
      (list c1))
    (implies (and (list y) (lseg x y)) (list x))
  )
)

; skolemized induction principle, recursive defs
(define-fun indr_lseglist ((x Int) (y Int)) Bool
  (implies
    (implies
      (and
        (or
         (= d2 -1)
         (and (not (= d2 -1))
              (and (list (next d2)) (not (select (hlseg (next d2) -1) d2))))
        )
        (or
          (and (= d1 d2) (= (hlseg d1 d2) emp))
          (and (and (not (= d1 d2))
                    (and (lseg (next d1) d2) (list (next d1))))
               (not (select (hlseg (next d1) d2) d1)))
        ))
      (list d1))
    (implies (lseg x y) (list x))
  )
)

(assert (unfoldlist c1))
(assert (unfoldlist (next c1)))
(assert (= (unfoldhlseg (next c1) -1) (hlseg (next c1) -1)))

; lemma about hlseg needed (see hlseg_lemmas)
(assert (implies (select (hlseg (next (next c1)) -1) c1)
                 (select (hlseg (next (next c1)) -1) (next c1))))


(assert (unfoldlist d1))
(assert (unfoldlist (next d1)))
(assert (= (unfoldhlseg (next d1) -1) (hlseg (next d1) -1)))

; lemma about hlseg needed (see hlseg_lemmas)
(assert (implies (select (hlseg (next (next d1)) -1) d1)
                 (select (hlseg (next (next d1)) -1) (next d1))))

;;;;;;;;; lseglist

(echo "no induction principle:")
(push)
(assert (not (prop_lseglist a b)))
(check-sat)
(pop)

(echo "")
(echo "with weaker induction principle:")
(push)
(assert (and (ind_lseglist a b) (not (prop_lseglist a b))))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_lseglist a b) (not (prop_lseglist a b))))
(check-sat)
(pop)


