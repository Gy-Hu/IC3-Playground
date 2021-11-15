(declare-rel Invariant (Bool Bool Bool Bool))
(declare-rel Goal ())
(declare-var l0 Bool) ;xn3
(declare-var l2 Bool)  ;i2?
(declare-var l4 Bool) ;x1
(declare-var l6 Bool) ;x2
(declare-var l8 Bool) ;x3 ;xn1
(declare-var l10 Bool) ;x4
(declare-var l12 Bool) ;xn1
(declare-var l14 Bool) ;xn4
(declare-var l16 Bool) ;i1
(rule (=> (not (or l4 l6 l8 l10)) (Invariant l4 l6 l8 l10)))
(rule (=> (and (Invariant l4 l6 l8 l10)
  (= (and l6 l4) l12)
  (= (and l12 l8) l14)
  (= (and l10 (not l0)) l16)
  ) (Invariant l12 l8 l0 l14)))
(rule (=> (and (Invariant l4 l6 l8 l10)
  (= (and l10 (not l0)) l16)
  l16) Goal))
(query Goal) ;#TODO: test the "let"



