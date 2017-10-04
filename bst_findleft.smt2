(define-sort Set (T) (Array T Bool))

; bst, key
(declare-fun bst (Int) Bool)
(declare-fun hbst (Int) (Set Int))

(declare-fun key (Int) Int)
(declare-fun keys (Int) (Set Int))

(declare-fun find-leftmost ((Int) (Int)) Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

; empty set
(declare-const emp (Set Int))
(assert (= emp ((as const (Set Int)) false)))

(declare-fun left (Int) Int)
(assert (= (left -1) -1))

(declare-fun right (Int) Int)
(assert (= (right -1) -1))

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

; macro for unfolding hbst
(define-fun unfoldhbst ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton x) (union (hbst (left x)) (hbst (right x)))))
)

; macro for unfolding keys
(define-fun unfoldkeys ((x Int)) (Set Int)
  (ite (= x -1) emp (union (singleton (key x)) (union (keys (left x)) (keys (right x)))))
)

; macro for unfolding sorted list
(define-fun unfoldbst ((x Int)) Bool
  (iff (bst x)
       (or
         (or (= x -1) (and (= (left x) -1) (= (right x) -1)))
         (and (and (<= (key (left x)) (key x)) (<= (key x) (key (right x)))
                   (and (and (bst (left x)) (bst (right x)))
                        (and (not (select (hbst (left x)) x))
                             (not (select (hbst (right x)) x))))))
       )
  )
)

; macro for unfolding find-last
(define-fun unfold-find-leftmost ((x Int) (v Int)) Bool
  (iff (find-leftmost x v)
       (or
         (and (= (left x) -1) (= (key x) v))
         (and (not (= (left x) -1)) (find-leftmost (left x) v))
       )
  )
)

; sorted lseg -> sorted list
(define-fun prop-find-leftmost ((x Int)) Bool
  (implies (and (bst x) (find-leftmost x b)) (<= b (key x)))
)

; recursive induction principle
(define-fun indr-find-leftmost ((x Int)) Bool
  (implies
    (implies
      (and (or
             (or (= c -1) (and (= (left c) -1) (= (right c) -1)))
              (and (and (<= (key (left c)) (key c)) (<= (key c) (key (right c)))
                        (and (and (bst (left c)) (bst (right c)))
                             (and (not (select (hbst (left c)) c))
                                  (not (select (hbst (right c)) c))))))
           )
           (or
             (and (= (left c) -1) (= (key c) b))
             (and (not (= (left c) -1)) (and (find-leftmost (left c) b) (<= b (key (left c)))))
           ))
      (<= b (key c)))
    (implies (and (bst x) (find-leftmost x b)) (<= b (key x)))
  )
)

(echo "no induction principle:")
(push)
(assert (not (prop-find-leftmost a)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr-find-leftmost a) (not (prop-find-leftmost a))))
(check-sat)
(pop)


