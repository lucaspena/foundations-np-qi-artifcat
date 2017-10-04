(define-sort Set (T) (Array T Bool))

(declare-fun hlseg ((Int) (Int) (Set Int)) Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)

(declare-const H2 (Set Int))
(declare-const H3 (Set Int))
(declare-const H4 (Set Int))
(declare-const Hs (Set Int))
(declare-const Hns (Set Int))
(declare-const Hd (Set Int))
(declare-const He (Set Int))

; empty set
(declare-const emp (Set Int))
(assert (= emp ((as const (Set Int)) false)))

(declare-fun next (Int) Int)
(assert (= (next -1) -1))

; singleton set
(define-fun singleton ((x Int)) (Set Int)
  (store emp x true)
)

; macro for unfolding hlseg
(define-fun unfoldhlseg ((x Int) (y Int) (H (Set Int))) Bool
  (iff (hlseg x y H)
       (or
         (and (= x y) (= H emp))
         (and (not (= x y)) (and (= H (union H2 (singleton x))) (hlseg (next x) y H2)))
       )
  )
)

; prop to prove: if z \in hlseg(n(x), y), then z \in hlseg(x, y)
(define-fun prop_hlseg ((x Int) (y Int) (z Int) (H (Set Int)) (Hn (Set Int))) Bool
  (implies (and (and (and (not (= x y)) (hlseg x y H)) (hlseg (next x) y Hn)) (select Hn z))
           (select H z))
)

(assert (= (unfoldhlseg a b Hd) (hlseg a b Hd)))
(assert (= H2 He))

(echo "no induction principle:")
(push)
(assert (not (prop_hlseg a b c Hd He)))
(check-sat)
(pop)

