(define-sort Set (T) (Array T Bool))

(declare-fun list (Int) Bool)
(declare-fun hlseg ((Int) (Int)) (Set Int))
(declare-fun lseg ((Int) (Int)) Bool)

(declare-const v Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const c4 Int)
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

; lseg linord
(define-fun lseglinord ((y Int)) Bool
  (or (lseg y d1) (lseg d1 y))
)

; prop to prove: if x->d1 is an lseg, then so is either y->d1 or d1->y
(define-fun prop_lseglinord ((x Int) (y Int)) Bool
  (implies (and (lseg x y) (lseg x d1)) (lseglinord y))
)
  

; skolemized induction principle for lseg_linord, no recursive defs
(define-fun ind_lseglinord ((x Int) (y Int)) Bool
  (implies
    (implies
      (and (or
             (and (= c1 c2) (= (hlseg c1 c2) emp))
             (and (and (not (= c1 c2))
                       (lseglinord c2))
                  (not (select (hlseg (next c1) c2) c1)))
           )
           (or
             (and (= c1 d1) (= (hlseg c1 d1) emp))
             (and (and (not (= c1 d1))
                       (lseglinord d1))
                  (not (select (hlseg (next c1) d1) c1)))
           )
      )
      (lseglinord c2))
    (prop_lseglinord x y)
  )
) 

; skolemized induction principle for lseg_linord, with recursive defs
(define-fun indr_lseglinord ((x Int) (y Int)) Bool
  (implies
    (implies
      (and (or
             (and (= c3 c4) (= (hlseg c3 c4) emp))
             (and (and (not (= c3 c4))
                       (and (lseg (next c3) c4) (lseglinord c4)))
                  (not (select (hlseg (next c3) c4) c3)))
           )
           (or
             (and (= c3 d1) (= (hlseg c3 d1) emp))
             (and (and (not (= c3 d1))
                       (and (lseg (next c3) d1) (lseglinord d1)))
                  (not (select (hlseg (next c3) d1) c3)))
           )
      )
      (lseglinord c4))
    (prop_lseglinord x y)
  )
)

(assert (unfoldlseg c1 d1))
(assert (unfoldlseg c3 d1))

(echo "no induction principle:")
(push)
(assert (not (prop_lseglinord a b)))
(check-sat)
(pop)

(echo "")
(echo "with weaker induction principle:")
(push)
(assert (and (ind_lseglinord a b) (not (prop_lseglinord a b))))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_lseglinord a b) (not (prop_lseglinord a b))))
(check-sat)
(pop)
