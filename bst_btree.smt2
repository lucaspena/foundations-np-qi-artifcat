(define-sort Set (T) (Array T Bool))

; bst, key
(declare-fun btree (Int) Bool)
(declare-fun bst (Int) Bool)
(declare-fun hbst (Int) (Set Int))

(declare-fun key (Int) Int)

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

; macro for unfolding binary tree
(define-fun unfoldbtree ((x Int)) Bool
  (iff (btree x)
       (or
         (or (= x -1) (and (= (left x) -1) (= (right x) -1)))
         (and (and (btree (left x)) (btree (right x)))
              (and (not (select (hbst (left x)) x))
                   (not (select (hbst (right x)) x))))
       )
  )
)

; macro for unfolding bst
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

; bst -> btree
(define-fun prop_bst-btree ((x Int)) Bool
  (implies (bst x) (btree x))
)

; recursive induction principle
(define-fun indr_bst-btree ((x Int)) Bool
  (implies
    (implies
      (or
        (or (= c -1) (and (= (left c) -1) (= (right c) -1)))
        (and (and (<= (key (left c)) (key c)) (<= (key c) (key (right c)))
                  (and (and (and (btree (left c)) (btree (right c)))
                            (and (bst (left c)) (bst (right c))))
                       (and (not (select (hbst (left c)) c))
                            (not (select (hbst (right c)) c))))))
      )
      (btree c))
    (prop_bst-btree x)
  )
)

(assert (unfoldbtree c))

(echo "no induction principle:")
(push)
(assert (not (prop_bst-btree a)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_bst-btree a) (not (prop_bst-btree a))))
(check-sat)
(pop)


