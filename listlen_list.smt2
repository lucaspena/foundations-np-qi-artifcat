(define-sort Set (T) (Array T Bool))

(declare-fun list (Int) Bool)
(declare-fun listlen ((Int) (Int)) Bool)
(declare-fun hlist (Int) (Set Int))

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

; macro for unfolding list
(define-fun unfoldlist ((x Int)) Bool
  (iff (list x)
       (or
         (= x -1)
         (and (not (= x -1))
              (and (list (next x)) (not (select (hlist (next x)) x))))
       )
  )
)

; macro for unfolding list with length
(define-fun unfoldlistlen ((x Int) (y Int)) Bool
  (iff (listlen x y)
       (or
         (and (= x -1) (= y 0))
         (and (and (not (= x -1)) (> y 0))
              (and (and (listlen (next x) v) (= v (- y 1))) (not (select (hlist (next x)) x))))
       )
  )
)

; list with length as field -> list
(define-fun prop_listlen-list ((x Int) (y Int)) Bool
  (implies (listlen x y) (list x))
)

; recursive induction principle
(define-fun indr_listlen-list ((x Int) (y Int)) Bool
  (implies
    (implies
       (or
         (and (= c -1) (= d 0))
         (and (and (not (= c -1)) (> d 0))
              (and (and (and (listlen (next c) v2) (list (next c))) (= v2 (- d 1)))
                   (not (select (hlist (next c)) c))))
       )
      (list c))
    (implies (listlen x y) (list x))
  )
)

(assert (unfoldlist c))

(echo "no induction principle:")
(push)
(assert (not (prop_listlen-list a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_listlen-list a b) (not (prop_listlen-list a b))))
(check-sat)
(pop)


