(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun dlist (Int) Bool)
(declare-fun hlsegf ((Int) (Int)) (Set Int))
(declare-fun hlsegb ((Int) (Int)) (Set Int))
(declare-fun dlseg ((Int) (Int)) Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c1 Int)
(declare-const c2 Int)

; empty set
(declare-const emp (Set Int))
(assert (= emp ((as const (Set Int)) false)))

(declare-fun next (Int) Int)
(assert (= (next -1) -1))

(declare-fun prev (Int) Int)
(assert (= (prev -1) -1))

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

; macro for unfolding hlseg (forwards)
; note that hlsegf with y as nil (-1) corresponds to the heaplet for the list from x
(define-fun unfoldhlsegf ((x Int) (y Int)) (Set Int)
  (ite (= x y) emp (union (singleton x) (union (hlsegf (next x) y))))
)

; macro for unfolding hlseg (backwards)
(define-fun unfoldhlsegb ((x Int) (y Int)) (Set Int)
  (ite (= x y) emp (union (singleton y) (union (hlsegb x (prev y)))))
)

; macro for unfolding doubly linked list
(define-fun unfolddlist ((x Int)) Bool
  (iff (dlist x)
       (or
         (or (= x -1) (= (next x) -1))
         (and (and (and (not (= x -1)) (not (= (next x) -1)))
                   (and (and (= (prev (next x)) x) (dlist (next x)))
                        (and (not (select (hlsegf (next x) -1) x))
                             (not (select (hlsegb -1 (prev x)) x))))))
       )
  )
)

; macro for unfolding doubly linked lseg
(define-fun unfolddlseg ((x Int) (y Int)) Bool
  (iff (dlseg x y)
       (or
         (and (= x y) (= (hlsegf x y) emp))
         (and (and (not (= x y))
                   (and (= (prev (next x)) x) (dlseg (next x) y))
                   (and (not (select (hlsegf (next x) y) x))
                        (and (not (select (hlsegb x (prev y)) y))
                             (not (select (hlsegb -1 (prev x)) x))))))
       )
  )
)

; sorted lseg -> doubly linked list
(define-fun prop_dlseglist ((x Int) (y Int)) Bool
  (implies (and (dlseg x y) (dlist y)) (dlist x))
)

; recursive induction principle
(define-fun indr_dlseglist ((x Int) (y Int)) Bool
  (implies
    (implies
      (and
        (or
          (or (= c2 -1) (= (next c2) -1))
          (and (and (and (not (= c2 -1)) (not (= (next c2) -1)))
                    (and (and (= (prev (next c2)) c2) (dlist (next c2)))
                         (and (not (select (hlsegf (next c2) -1) c2))
                              (not (select (hlsegb -1 (prev c2)) c2))))))
        )
        (or
          (and (= c1 c2) (= (hlsegf c1 c2) emp))
          (and (and (not (= c1 c2))
                    (and (= (prev (next c1)) c1) (and (dlseg (next c1) c2) (dlist (next c1))))
                    (and (not (select (hlsegf (next c1) c2) c1))
                         (and (not (select (hlsegb c1 (prev c2)) c2))
                              (not (select (hlsegb -1 (prev c1)) c1))))))
        ))
      (dlist c1))
    (prop_dlseglist x y)
  )
)

(assert (unfolddlist c1))
(assert (unfolddlist (next c1)))
(assert (unfolddlseg (next c1) c2))
(assert (= (unfoldhlsegf (next c1) -1) (hlsegf (next c1) -1)))
(assert (= (unfoldhlsegf (next c2) -1) (hlsegf (next c2) -1)))

; lemma about hlsegf needed (see hlseg_lemma.smt2)
(assert (implies (select (hlsegf (next (next c1)) -1) c1)
                 (select (hlsegf (next (next c1)) -1) (next c1))))

(echo "no induction principle:")
(push)
(assert (not (prop_dlseglist a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_dlseglist a b) (not (prop_dlseglist a b))))
(check-sat)
(pop)
