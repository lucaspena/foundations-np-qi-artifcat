(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun list (Int) Bool)
(declare-fun dlist (Int) Bool)

(declare-fun hlist (Int) (Set Int))
(declare-fun key (Int) Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

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

; dlist implies list
(define-fun prop_dlist-list ((x Int)) Bool
  (implies (dlist x) (list x))
)

; recursive induction principle
(define-fun indr_dlist-list ((x Int)) Bool
  (implies
    (implies
       (or
         (or (= c -1) (= (next c) -1))
         (and (and (and (not (= c -1)) (not (= (next c) -1)))
                   (and (and (list (next c)) (and (dlist (next c)) (= (prev (next c)) c)))
                        (not (select (hlist (next c)) c)))))
       )
      (list c))
    (implies (dlist x) (list x))
  )
)

(assert (unfoldlist c))
(assert (unfoldlist (next c)))
(assert (= (hlist (next c)) (unfoldhlist (next c))))

(echo "no induction principle:")
(push)
(assert (not (prop_dlist-list a)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_dlist-list a) (not (prop_dlist-list a))))
(check-sat)
(pop)


