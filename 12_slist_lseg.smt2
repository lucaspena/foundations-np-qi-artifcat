(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun slist (Int) Bool)
(declare-fun hlseg ((Int) (Int)) (Set Int))
(declare-fun slseg ((Int) (Int)) Bool)

(declare-fun key (Int) Int)

(declare-const a Int)
(declare-const b Int)
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
; note that hlseg with y as nil (-1) corresponds to the heaplet for the list from x
(define-fun unfoldhlseg ((x Int) (y Int)) (Set Int)
  (ite (= x y) emp (union (singleton x) (hlseg (next x) y)))
)

; macro for unfolding sorted list
(define-fun unfoldslist ((x Int)) Bool
  (iff (slist x)
       (or
         (or (= x -1) (= (next x) -1))
         (and (and (and (not (= x -1)) (not (= (next x) -1))) (<= (key x) (key (next x)))
                   (and (slist (next x)) (not (select (hlseg (next x) -1) x)))))
       )
  )
)

; macro for unfolding sorted lseg
(define-fun unfoldslseg ((x Int) (y Int)) Bool
  (iff (slseg x y)
       (or
         (and (= x y) (= (hlseg x y) emp))
         (and (and (and (not (= x y)) (<= (key x) (key (next x))) (slseg (next x) y))
                   (not (select (hlseg (next x) y) x))))
       )
  )
)

; sorted lseg -> sorted list
(define-fun prop_slseglist ((x Int) (y Int)) Bool
  (implies (and (slist y) (slseg x y)) (slist x))
)

; recursive induction principle
(define-fun indr_slseglist ((x Int) (y Int)) Bool
  (implies
    (implies
      (and
        (or
          (or (= d -1) (= (next d) -1))
          (and (and (and (not (= d -1)) (not (= (next d) -1))) (<= (key d) (key (next d)))
                    (and (slist (next d)) (not (select (hlseg (next d) -1) d)))))
        )
        (or
          (and (= c d) (= (hlseg c d) emp))
          (and (and (and (not (= c d)) (<= (key c) (key (next c)))
                         (and (slseg (next c) d) (slist (next c)))))
               (not (select (hlseg (next c) d) c)))
        ))
      (slist c))
    (prop_slseglist x y)
  )
)

(assert (unfoldslist c))
(assert (unfoldslist (next c)))
(assert (= (unfoldhlseg (next c) -1) (hlseg (next c) -1)))
(assert (= (unfoldhlseg (next (next c)) -1) (hlseg (next (next c)) -1)))

; lemma about hlseg needed (see hlseg_lemma.smt2)
(assert (implies (select (hlseg (next (next c)) -1) c)
                 (select (hlseg (next (next c)) -1) (next c))))

(echo "no induction principle:")
(push)
(assert (not (prop_slseglist a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_slseglist a b) (not (prop_slseglist a b))))
(check-sat)
(pop)


