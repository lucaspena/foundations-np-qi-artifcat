(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun list (Int) Bool)
(declare-fun dlist (Int) Bool)

(declare-fun hlistf (Int) (Set Int))
(declare-fun hlistb (Int) (Set Int))
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

; macro for unfolding hlistf
(define-fun unfoldhlistf ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlistf (next x))))
)

; macro for unfolding hlistb
(define-fun unfoldhlistb ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlistb (prev x))))
)

; macro for unfolding list
(define-fun unfoldlist ((x Int)) Bool
  (iff (list x)
       (or
         (= x -1)
         (and (not (= x -1))
              (and (list (next x)) (not (select (hlistf (next x)) x))))
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
                        (and (not (select (hlistf (next x)) x))
                             (not (select (hlistb (prev x)) x))))))
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
                        (and (not (select (hlistf (next c)) c))
                             (not (select (hlistb (prev c)) c))))))
       )
      (list c))
    (prop_dlist-list x)
  )
)

(assert (unfoldlist c))
(assert (unfoldlist (next c)))
(assert (= (hlistf (next c)) (unfoldhlistf (next c))))

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


