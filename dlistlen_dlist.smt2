(define-sort Set (T) (Array T Bool))

(declare-fun dlist (Int) Bool)
(declare-fun dlistlen ((Int) (Int)) Bool)
(declare-fun hlist (Int) (Set Int))
(declare-fun key (Int) Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)

(declare-const v Int)
(declare-const v2 Int)

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

; macro for unfolding hlist (forwards)
(define-fun unfoldhlist ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlist (next x))))
)

; macro for unfolding doubly linked list
(define-fun unfolddlist ((x Int)) Bool
  (iff (dlist x)
       (or
         (or (= x -1) (= (next x) -1))
         (and (and (and (not (= x -1)) (not (= (next x) -1)))
                   (and (and (= (prev (next x)) x) (dlist (next x)))
                        (not (select (hlist (next x)) x)))))
       )
  )
)

; macro for unfolding doubly linked list with length
(define-fun unfolddlistlen ((x Int) (y Int)) Bool
  (iff (dlistlen x y)
       (or
         (or (and (= x -1) (= y 0)) (and (= (next x) -1) (= y 1)))
         (and (and (and (not (= x -1)) (and (not (= (next x) -1)) (> y 1)))
                   (and (and (= (prev (next x)) x)
                             (and (dlistlen (next x) v) (= v (- y 1))))
                        (not (select (hlist (next x)) x)))))
       )
  )
)

; list with length as field -> list
(define-fun prop_dlistlen-list ((x Int) (y Int)) Bool
  (implies (dlistlen x y) (dlist x))
)

; recursive induction principle
(define-fun indr_dlistlen-list ((x Int) (y Int)) Bool
  (implies
    (implies
       (or
         (or (and (= c -1) (= d 0)) (and (= (next c) -1) (= d 1)))
         (and (and (and (not (= c -1)) (and (not (= (next c) -1)) (> d 1)))
                   (and (and (= (prev (next c)) c)
                             (and (and (dlistlen (next c) v2) (dlist (next c))) (= v2 (- d 1))))
                        (not (select (hlist (next c)) c)))))
       )
      (dlist c))
    (implies (dlistlen x y) (dlist x))
  )
)

(assert (unfolddlist c))

(echo "no induction principle:")
(push)
(assert (not (prop_dlistlen-list a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_dlistlen-list a b) (not (prop_dlistlen-list a b))))
(check-sat)
(pop)


