(define-sort Set (T) (Array T Bool))

(declare-fun list (Int) Bool)
(declare-fun hlseg ((Int) (Int)) (Set Int))
(declare-fun lsegv (Int) Bool)

(declare-const a Int)
(declare-const v Int)
(declare-const c Int)
(declare-const d Int)

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

; end of lseg assumed to be a list
(assert (list v))

; macro for unfolding lsegv (unary)
(define-fun unfoldlsegv ((x Int)) Bool
  (iff (lsegv x)
       (or
         (and (= x v) (= (hlseg x v) emp))
         (and (and (not (= x v)) (lsegv (next x))) (not (select (hlseg (next x) v) x)))
       )
  )
)

; prop to prove: if x is an lseg, it is a list (since v is assumed to be a list)
(define-fun prop ((x Int)) Bool
  (implies (lsegv x) (list x))
)

; skolemized induction principle, no recursive definitions
(define-fun ind ((x Int)) Bool
  (implies
    (implies
      (or
        (and (= c v) (= (hlseg c v) emp))
        (and (and (not (= c v))
                  (list (next c)))
             (not (select (hlseg (next c) v) c)))
      )
      (list c))
    (implies (lsegv x) (list x))
  )
)

; skolemized induction principle, recursive defs
(define-fun indr ((x Int)) Bool
  (implies
    (implies
      (and (or
             (and (= d v) (= (hlseg d v) emp))
             (and (and (not (= d v))
                       (and (lsegv (next d)) (list (next d))))
                  (not (select (hlseg (next d) v) d)))
           )
           (or
             (= v -1)
             (and (not (= v -1))
                  (and (list (next v)) (not (select (hlseg (next v) -1) v))))
           ))
      (list d))
    (implies (lsegv x) (list x))
  )
)

(assert (unfoldlist c))
(assert (unfoldlist (next c)))
(assert (= (unfoldhlseg (next c) -1) (hlseg (next c) -1)))

; lemma about hlseg needed (see hlseg_lemmas)
(assert (implies (select (hlseg (next (next c)) -1) c)
                 (select (hlseg (next (next c)) -1) (next c))))


(assert (unfoldlist d))
(assert (unfoldlist (next d)))
(assert (= (unfoldhlseg (next d) -1) (hlseg (next d) -1)))

; lemma about hlseg needed (see hlseg_lemmas)
(assert (implies (select (hlseg (next (next d)) -1) d)
                 (select (hlseg (next (next d)) -1) (next d))))


(echo "no induction principle:")
(push)
(assert (not (prop a)))
(check-sat)
(pop)

(echo "")
(echo "with weaker induction principle:")
(push)
(assert (and (ind a) (not (prop a))))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr a) (not (prop a))))
(check-sat)
(pop)
