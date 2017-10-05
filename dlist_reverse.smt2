(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun dlist (Int) Bool)
(declare-fun hlistf (Int) (Set Int))
(declare-fun hlistb (Int) (Set Int))
(declare-fun reverse ((Int) (Int)) Bool)

(declare-fun key (Int) Int)
(declare-fun keys (Int) (Set Int))

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

(define-fun unfoldkeys ((x Int)) (Set Int)
  (union (singleton (key x)) (keys (next x)))
)

; macro for unfolding hlistf
(define-fun unfoldhlistf ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlistf (next x))))
)

; macro for unfolding hlistb
(define-fun unfoldhlistb ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlistb (prev x))))
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

; macro for unfolding reverse
(define-fun unfoldrev ((x Int) (y Int)) Bool
  (iff (reverse x y)
       (or
         (and (= x -1) (= y -1))
         (and (= x y) (reverse (next x) (prev y)))
       )
  )
)

; reverse has same keys
(define-fun prop_revkeys ((x Int) (y Int)) Bool
  (implies (reverse x y) (= (keys x) (keys y)))
)

; recursive induction principle
(define-fun indr_revkeys ((x Int) (y Int)) Bool
  (implies
    (implies
      (or
        (and (= c1 -1) (= c2 -1))
        (and (= c1 c2) (and (reverse (next c1) (prev c2)) (= (keys (next c1)) (keys (prev c2)))))
      )
      (= (keys c1) (keys c2)))
    (prop_revkeys x y)
  )
)

(assert (and (dlist a) (dlist b)))

(echo "no induction principle:")
(push)
(assert (not (prop_revkeys a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_revkeys a b) (not (prop_revkeys a b))))
(check-sat)
(pop)


