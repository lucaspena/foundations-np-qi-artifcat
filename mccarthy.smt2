; mccarthy 91 function

; mccarthy 91 function as a relation, with skolemized function
(declare-fun mccarthy ((Int) (Int)) Bool)
(declare-fun g ((Int) (Int)) Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)

; macro for unfolding mccarthy
(define-fun unfoldmccarthy ((n Int) (m Int)) Bool
  (iff (mccarthy n m)
       (or
         (and (> n 100) (= m (- n 10)))
         (and (<= n 100) (and (mccarthy (+ n 11) (g n m)) (mccarthy (g n m) m)))
       )
  )
)

; closed-form formula
(define-fun prop_mccarthy ((n Int) (m Int)) Bool
  (implies (mccarthy n m) (or (> n 100) (= m 91)))
)

(define-fun indr_mccarthy ((n Int) (m Int)) Bool
  (implies
    (implies
       (or
         (and (> c 100) (= d (- c 10)))
         (and (<= c 100) (and (and (or (> (+ c 11) 100) (= (g c d) 91))
                                  (or (> (g c d) 100) (= m 91)))
                             (and (mccarthy (+ c 11) (g c d)) (mccarthy (g c d) d))))
       )
      (or (> c 100) (= d 91)))
      (implies (mccarthy n m) (or (> n 100) (= m 91)))
   )
)

(assert (unfoldmccarthy (+ c 11) (g c d)))
(assert (unfoldmccarthy (g c d) d))

(echo "no induction principle:")
(push)
(assert (not (prop_mccarthy a b)))
(check-sat)
(pop)

(echo "")
(echo "with stronger induction principle:")
(push)
(assert (and (indr_mccarthy a b) (not (prop_mccarthy a b))))
(check-sat)
(pop)
