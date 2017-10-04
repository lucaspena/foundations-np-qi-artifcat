(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun list (Int) Bool)
(declare-fun slist (Int) Bool)
(declare-fun hlist (Int) (Set Int))
(declare-fun key (Int) Int)

(declare-const a Int)
(declare-const c Int)

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

; sorted list -> list
(define-fun prop_slist-list ((x Int)) Bool
  (implies (slist x) (list x))
)

; recursive induction principle
(define-fun indr_slist-list ((x Int)) Bool
  (implies
    (implies
       (or
         (or (= c -1) (= (next c) -1))
         (and (and (and (not (= c -1)) (not (= (next c) -1))) (<= (key c) (key (next c)))
                   (and (and (list (next c)) (slist (next c))) (not (select (hlist (next c)) c)))))
       )
      (list c))
    (implies (slist x) (list x))
  )
)

(assert (unfoldlist (next c)))
(assert (unfoldlist c))
(assert (= (hlist (next c)) (unfoldhlist (next c))))

(echo "no induction principle:")
(push)
(assert (not (prop_slist-list a)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_slist-list a) (not (prop_slist-list a))))
(check-sat)
(pop)


