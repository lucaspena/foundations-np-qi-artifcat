(define-sort Set (T) (Array T Bool))

(declare-fun slist (Int) Bool)
(declare-fun slistlen ((Int) (Int)) Bool)
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

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

; macro for unfolding hlist
(define-fun unfoldhlist ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlist (next x))))
)

; macro for unfolding sorted list
(define-fun unfoldslist ((x Int)) Bool
  (iff (slist x)
       (or
         (or (= x -1) (= (next x) -1))
         (and (and (and (not (= x -1)) (not (= (next x) -1))) (<= (key x) (key (next x)))
                   (and (slist (next x)) (not (select (hlist (next x)) x)))))
       )
  )
)

; macro for unfolding sorted list
(define-fun unfoldslistlen ((x Int) (y Int)) Bool
  (iff (slistlen x y)
       (or
         (or (and (= x -1) (= y 0)) (and (= (next x) -1) (= y 1)))
         (and (and (and (and (not (= x -1)) (not (= (next x) -1))) (> y 1))
                   (<= (key x) (key (next x)))
                   (and (and (slistlen (next x) v) (= v (- y 1)))
                        (not (select (hlist (next x)) x)))))
       )
  )
)

; list with length as field -> list
(define-fun prop_slistlen-list ((x Int) (y Int)) Bool
  (implies (slistlen x y) (slist x))
)

; recursive induction principle
(define-fun indr_slistlen-list ((x Int) (y Int)) Bool
  (implies
    (implies
       (or
         (or (and (= c -1) (= d 0)) (and (= (next c) -1) (= d 1)))
         (and (and (and (and (not (= c -1)) (not (= (next c) -1))) (> d 1))
                   (<= (key c) (key (next c)))
                   (and (and (and (slistlen (next c) v2) (slist (next c))) (= v2 (- d 1)))
                        (not (select (hlist (next c)) c)))))
       )
      (slist c))
    (implies (slistlen x y) (slist x))
  )
)

(assert (unfoldslist c))

(echo "no induction principle:")
(push)
(assert (not (prop_slistlen-list a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_slistlen-list a b) (not (prop_slistlen-list a b))))
(check-sat)
(pop)


