(define-sort Set (T) (Array T Bool))

; sorted list, key
(declare-fun slist (Int) Bool)
(declare-fun hlsegf (Int) (Set Int))
(declare-fun hlsegb (Int) (Set Int))
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

; macro for unfolding hlseg (forwards)
(define-fun unfoldhlsegf ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlsegf (next x))))
)

; macro for unfolding hlseg (backwards)
(define-fun unfoldhlsegb ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (hlsegb (prev x))))
)

; macro for unfolding sorted list
(define-fun unfoldslist ((x Int)) Bool
  (iff (slist x)
       (or
         (or (= x -1) (= (next x) -1))
         (and (and (and (not (= x -1)) (not (= (next x) -1))) (<= (key x) (key (next x)))
                   (and (slist (next x))
                        (and (not (select (hlsegf (next x)) x))
                             (not (select (hlsegb (prev x)) x))))))
       )
  )
)

; macro for unfolding sorted lseg
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
    (implies (reverse x y) (= (keys x) (keys y)))
  )
)

(assert (and (slist a) (slist b)))

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


