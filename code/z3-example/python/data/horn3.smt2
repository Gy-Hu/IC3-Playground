(declare-rel Invariant (Bool))
(declare-rel Goal ())
(declare-var l0 Bool) ;ignore
(declare-var l2 Bool) ;i1
(declare-var l4 Bool) ;x1
(declare-var l6 Bool) ;i2
(declare-var l8 Bool) ;i3
(declare-var l10 Bool) ;xn1
(rule (=> (not (or l4)) (Invariant l4)))
(rule (=> (and (Invariant l4)
  (= (and (not l4) (not l2)) l6) ;l2 is i1, l6 is i2
  (= (and l4 l2) l8) ;l8 is i3
  (= (and (not l8) (not l6)) l10)
  ) (Invariant l10))) ;l10 is xn1
(rule (=> (and (Invariant l4) ;l4 is x1
  l4) Goal))
(query Goal)
